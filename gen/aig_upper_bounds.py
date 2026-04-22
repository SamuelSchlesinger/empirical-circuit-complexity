#!/usr/bin/env python3
"""
Use ABC (Berkeley's AIG minimization tool) to find small AIG implementations
of Boolean functions, then convert them to Lean 4 upper bound proof terms.

The project's circuit model (AND gates with free wire negation) is exactly
an AIG (And-Inverter Graph), so ABC's minimized AIGs translate directly to
Lean Circuit terms.

For each representative function, produces:
  - f_{idx}_size : Nat := k
  - f_{idx}_upper : HasCircuitOfSize ... k := ⟨witness, decide⟩

Usage:
  python3 gen/aig_upper_bounds.py 2           # all Size2 representatives
  python3 gen/aig_upper_bounds.py 3           # all Size3 representatives
  python3 gen/aig_upper_bounds.py 2 3         # both
  python3 gen/aig_upper_bounds.py --func 6 2  # just f_6 for n=2
  python3 gen/aig_upper_bounds.py --write 2   # write Proofs files directly

Requires: yosys-abc (or abc) in PATH, or specify --abc-path.
"""

import argparse
import math
import os
import subprocess
import sys
import tempfile
from itertools import permutations


# ================================================================
# Representative computation (reused from generate.py)
# ================================================================

def num_functions(n):
    return 2 ** (2 ** n)


def truth_value(func_idx, input_idx):
    return (func_idx >> input_idx) & 1


def apply_perm_to_input_idx(perm, j, n):
    j_prime = 0
    for i in range(n):
        bit = (j >> perm[i]) & 1
        j_prime |= bit << i
    return j_prime


def apply_perm_to_func(perm, func_idx, n):
    num_inputs = 1 << n
    new_idx = 0
    for j in range(num_inputs):
        j_prime = apply_perm_to_input_idx(perm, j, n)
        bit = (func_idx >> j_prime) & 1
        new_idx |= bit << j
    return new_idx


def apply_input_negation(func_idx, neg_mask, n):
    num_inputs = 1 << n
    new_idx = 0
    for j in range(num_inputs):
        j_prime = j ^ neg_mask
        bit = (func_idx >> j_prime) & 1
        new_idx |= bit << j
    return new_idx


def compute_representatives(n):
    total = num_functions(n)
    output_neg_mask = total - 1
    rep_of = {}

    for func_idx in range(total):
        if func_idx in rep_of:
            continue
        orbit = set()
        for perm in permutations(range(n)):
            permuted = apply_perm_to_func(list(perm), func_idx, n)
            for neg_mask in range(1 << n):
                negated = apply_input_negation(permuted, neg_mask, n)
                orbit.add(negated)
                orbit.add(negated ^ output_neg_mask)
        rep = min(orbit)
        for idx in orbit:
            rep_of[idx] = rep

    reps = sorted(set(rep_of.values()))
    return reps, rep_of


# ================================================================
# ABC interface
# ================================================================

def find_abc(abc_path=None):
    """Find ABC binary. Tries yosys-abc, then abc."""
    if abc_path:
        return abc_path
    for name in ["yosys-abc", "abc"]:
        try:
            subprocess.run([name, "-c", "quit"], capture_output=True, timeout=5)
            return name
        except (FileNotFoundError, subprocess.TimeoutExpired):
            continue
    return None


def func_to_pla(n, func_idx):
    """Convert function truth table to PLA format.

    PLA row ordering: for each minterm j, input bits are listed left-to-right
    as x_0, x_1, ..., x_{n-1} (matching our little-endian convention).
    This ensures ABC's PI 0 = our x_0, PI 1 = our x_1, etc.
    """
    lines = [f".i {n}", ".o 1"]
    for j in range(1 << n):
        input_bits = "".join(str((j >> i) & 1) for i in range(n))
        output_bit = str((func_idx >> j) & 1)
        lines.append(f"{input_bits} {output_bit}")
    lines.append(".e")
    return "\n".join(lines)


def our_tt_to_abc_hex(func_idx, n):
    """Convert our truth table encoding to ABC's exact command hex format.

    ABC's exact command uses MSB variable ordering (variable 0 = MSB of
    minterm index), while our encoding uses LSB variable ordering (x_0 = bit 0).
    We reverse the bit order of each minterm index to convert.
    """
    num_bits = 1 << n
    abc_tt = 0
    for j in range(num_bits):
        if (func_idx >> j) & 1:
            j_abc = int(format(j, f"0{n}b")[::-1], 2)
            abc_tt |= 1 << j_abc
    hex_digits = max(1, num_bits // 4)
    return format(abc_tt, f"0{hex_digits}x")


def run_abc(abc_path, commands):
    """Run ABC with a sequence of commands. Returns (success, stdout, stderr)."""
    cmd_str = "; ".join(commands)
    result = subprocess.run(
        [abc_path, "-c", cmd_str],
        capture_output=True, text=True, timeout=60,
    )
    return result.returncode == 0, result.stdout, result.stderr


def minimize_with_pla(abc_path, n, func_idx, aig_path):
    """Minimize using PLA input + aggressive AIG optimization passes."""
    pla_content = func_to_pla(n, func_idx)

    with tempfile.NamedTemporaryFile(
        suffix=".pla", mode="w", delete=False
    ) as f:
        f.write(pla_content)
        pla_path = f.name

    try:
        # Aggressive optimization: multiple rounds of rewriting
        opt = "balance; rewrite; refactor; balance; rewrite; rewrite -z; balance; refactor -z; rewrite -z; balance"
        cmds = [
            f"read_pla {pla_path}",
            "strash",
            "dc2",
            opt,
            "dc2",
            opt,
            "dc2",
            opt,
            f"write_aiger {aig_path}",
            "quit",
        ]
        ok, stdout, stderr = run_abc(abc_path, cmds)
        return ok
    finally:
        os.unlink(pla_path)


def minimize_with_exact(abc_path, n, func_idx, aig_path):
    """Minimize using ABC's exact SAT-based synthesis (guaranteed optimal).

    Note: exact finds the minimum network in a general gate library,
    then st converts to AIG. The AIG may have more gates than the
    optimal AIG, but it's usually very good.

    Variable ordering: exact uses MSB convention, so we convert the truth
    table. After exact+st, PI 0 maps to the MSB variable of the truth table,
    which after our conversion corresponds to our x_{n-1}. We reverse the
    input mapping when converting to Lean.
    """
    abc_hex = our_tt_to_abc_hex(func_idx, n)
    cmds = [
        f"exact {abc_hex}",
        "st",
        # Further AIG optimization after conversion
        "dc2",
        "balance; rewrite; refactor; balance; rewrite; rewrite -z; balance; refactor -z; rewrite -z; balance",
        f"write_aiger {aig_path}",
        "quit",
    ]
    ok, stdout, stderr = run_abc(abc_path, cmds)
    return ok


def minimize_aig(abc_path, n, func_idx, use_exact=True):
    """Find a small AIG for the function using ABC.

    Tries both PLA-based optimization and exact synthesis (if enabled),
    returns the smaller result. Verifies correctness before returning.

    Returns (n_inputs, ands, output_lit, input_map) where input_map[i]
    gives the 0-based input wire index in our convention for AIGER PI i.
    """
    results = []

    # Approach 1: PLA-based (correct variable ordering)
    with tempfile.NamedTemporaryFile(suffix=".aig", delete=False) as f:
        aig_path = f.name
    try:
        if minimize_with_pla(abc_path, n, func_idx, aig_path):
            with open(aig_path, "rb") as f:
                data = f.read()
            ni, ands, out = parse_binary_aiger(data)
            # PLA approach: PI i = our x_i (identity mapping)
            input_map = list(range(n))
            if verify_circuit(n, func_idx, ni, ands, out, input_map):
                results.append((ni, ands, out, input_map))
    finally:
        if os.path.exists(aig_path):
            os.unlink(aig_path)

    # Approach 2: exact synthesis (reversed variable ordering)
    if use_exact and n <= 5:
        with tempfile.NamedTemporaryFile(suffix=".aig", delete=False) as f:
            aig_path = f.name
        try:
            if minimize_with_exact(abc_path, n, func_idx, aig_path):
                with open(aig_path, "rb") as f:
                    data = f.read()
                ni, ands, out = parse_binary_aiger(data)
                # exact approach: PI i = our x_{n-1-i} (reversed)
                input_map = list(reversed(range(n)))
                if verify_circuit(n, func_idx, ni, ands, out, input_map):
                    results.append((ni, ands, out, input_map))
        except Exception:
            pass  # exact may fail for some functions
        finally:
            if os.path.exists(aig_path):
                os.unlink(aig_path)

    if not results:
        return None

    # Return the result with fewest AND gates
    return min(results, key=lambda r: len(r[1]))


# ================================================================
# AIGER parsing
# ================================================================

def parse_binary_aiger(data):
    """Parse binary AIGER format.

    Returns (n_inputs, ands, output_lit) where:
    - n_inputs: number of primary inputs
    - ands: list of (lhs_lit, rhs0_lit, rhs1_lit) for each AND gate
    - output_lit: the output literal
    """
    nl = data.index(b"\n")
    header = data[:nl].decode()
    parts = header.split()
    assert parts[0] == "aig", f"Expected binary AIGER, got: {parts[0]}"
    M, I, L, O, A = (
        int(parts[1]),
        int(parts[2]),
        int(parts[3]),
        int(parts[4]),
        int(parts[5]),
    )
    assert L == 0, "Latches not supported (combinational circuits only)"
    assert O == 1, f"Expected 1 output, got {O}"

    pos = nl + 1

    # Read output literal (one line)
    nl2 = data.index(b"\n", pos)
    output_lit = int(data[pos:nl2].decode())
    pos = nl2 + 1

    # Read AND gates (delta encoded)
    def read_delta():
        nonlocal pos
        result = 0
        shift = 0
        while True:
            b = data[pos]
            pos += 1
            result |= (b & 0x7F) << shift
            shift += 7
            if not (b & 0x80):
                break
        return result

    ands = []
    for i in range(A):
        lhs_lit = (I + 1 + i) * 2
        d0 = read_delta()
        d1 = read_delta()
        rhs0 = lhs_lit - d0
        rhs1 = rhs0 - d1
        ands.append((lhs_lit, rhs0, rhs1))

    return I, ands, output_lit


# ================================================================
# Circuit verification
# ================================================================

def verify_circuit(n, func_idx, n_inputs, ands, output_lit, input_map):
    """Verify that the AIG circuit computes the expected function.

    input_map[i] gives the 0-based index in our convention for AIGER PI i.
    """
    assert n_inputs == n, f"Expected {n} inputs, got {n_inputs}"

    for j in range(1 << n):
        # Build input assignment: our x_i = bit i of j
        our_inputs = [(j >> i) & 1 == 1 for i in range(n)]

        # Map to AIGER PI ordering
        aiger_inputs = [our_inputs[input_map[pi]] for pi in range(n)]

        # Evaluate circuit
        wire = {}
        wire[0] = False
        wire[1] = True
        for pi in range(n):
            wire[2 * (pi + 1)] = aiger_inputs[pi]
            wire[2 * (pi + 1) + 1] = not aiger_inputs[pi]

        for lhs_lit, rhs0, rhs1 in ands:
            wire[lhs_lit] = wire[rhs0] and wire[rhs1]
            wire[lhs_lit + 1] = not wire[lhs_lit]

        actual = wire[output_lit]
        expected = truth_value(func_idx, j) == 1

        if actual != expected:
            return False

    return True


# ================================================================
# Lean code generation
# ================================================================

def aig_to_lean(n, n_inputs, ands, output_lit, input_map):
    """Convert an AIGER circuit to a Lean Circuit term.

    Returns (num_gates, circuit_term) where circuit_term is a string
    representing ⟨gates, output⟩ in Lean syntax.

    The Lean Circuit model:
    - Wire 0..n-1: input wires (Fin n)
    - Wire n+i: output of gate i
    - Gate i can reference wires 0..n+i-1
    - Ref: ⟨⟨wire_idx, by omega⟩, negated⟩
    - Gate: ⟨ref_lhs, ref_rhs⟩
    - GateList: .nil | .cons prev_gates gate
    - Circuit: ⟨gate_list, output_ref⟩
    """
    num_gates = len(ands)

    # Handle constant functions (output is literal 0 or 1, no gates needed
    # but our model requires 1 gate for constants)
    if output_lit <= 1 and num_gates == 0:
        return make_constant_circuit(n, output_lit == 1)

    # Handle wire-only circuits (output directly references an input)
    if num_gates == 0:
        var = output_lit >> 1
        neg = bool(output_lit & 1)
        our_wire = input_map[var - 1]  # AIGER var is 1-indexed
        return 0, format_circuit(n, 0, [], (our_wire, neg))

    # Build gate list, mapping AIGER variables to Lean wire indices.
    # AIGER: inputs are vars 1..n (PI 0..n-1), gates are vars n+1..n+k
    # Lean:  inputs are wires 0..n-1, gate outputs are wires n..n+k-1
    #
    # With input_map, AIGER PI i → our input input_map[i] → Lean wire input_map[i]
    # AIGER gate var v (1-indexed) → Lean wire n + (v - n - 1) = v - 1
    # But with remapped inputs, AIGER input var i+1 → Lean wire input_map[i]

    def aiger_lit_to_lean_ref(lit):
        """Convert an AIGER literal to (lean_wire_idx, negated)."""
        if lit <= 1:
            # Constant: we can't represent this directly as a wire reference.
            # This shouldn't happen in a well-formed AIG after strash, but
            # handle it by flagging for special treatment.
            return ("const", lit == 1)
        var = lit >> 1  # 1-indexed AIGER variable
        neg = bool(lit & 1)
        if var <= n:
            # Input variable: AIGER PI (var-1) → our input input_map[var-1]
            lean_wire = input_map[var - 1]
        else:
            # Gate output: AIGER gate var → Lean wire n + (var - n - 1) = var - 1
            lean_wire = var - 1
        return (lean_wire, neg)

    lean_gates = []
    for lhs_lit, rhs0_lit, rhs1_lit in ands:
        ref0 = aiger_lit_to_lean_ref(rhs0_lit)
        ref1 = aiger_lit_to_lean_ref(rhs1_lit)
        lean_gates.append((ref0, ref1))

    output_ref = aiger_lit_to_lean_ref(output_lit)

    # Check for constant references (literal 0 or 1 used as gate inputs).
    # If present, we need to add a helper gate AND(x₀, ¬x₀) = false first.
    has_const = any(
        r[0] == "const"
        for gate in lean_gates
        for r in gate
    ) or output_ref[0] == "const"

    if has_const:
        return make_circuit_with_constants(n, lean_gates, output_ref)

    return num_gates, format_circuit(n, num_gates, lean_gates, output_ref)


def make_constant_circuit(n, value):
    """Create a 1-gate circuit for a constant function.

    AND(x₀, ¬x₀) = false, then negate output for true.
    """
    # Gate 0: AND(x₀, ¬x₀) — inputs are wire 0 (x₀)
    gates = [((0, False), (0, True))]
    # Output: wire n (gate 0 output), negated if we want true
    output_ref = (n, value)  # negated=True → ¬false = true
    return 1, format_circuit(n, 1, gates, output_ref)


def make_circuit_with_constants(n, lean_gates, output_ref):
    """Handle circuits that use constant 0/1 by prepending AND(x₀, ¬x₀).

    Inserts a constant-false gate at position 0 and adjusts all
    subsequent wire indices.
    """
    # Prepend constant gate: AND(x₀, ¬x₀) = false
    const_gate = ((0, False), (0, True))
    const_wire = n  # wire index of the constant gate's output

    # Shift all existing gate wire references by +1 (for gate outputs only)
    def adjust_ref(ref):
        wire, neg = ref
        if wire == "const":
            # Replace constant reference with the new constant gate
            # const false → wire const_wire, not negated
            # const true → wire const_wire, negated (¬false = true)
            return (const_wire, neg)
        if wire >= n:
            # Gate output wire: shift by 1
            return (wire + 1, neg)
        return (wire, neg)

    adjusted_gates = [
        (adjust_ref(r0), adjust_ref(r1)) for r0, r1 in lean_gates
    ]
    adjusted_output = adjust_ref(output_ref)

    all_gates = [const_gate] + adjusted_gates
    num_gates = len(all_gates)
    return num_gates, format_circuit(n, num_gates, all_gates, adjusted_output)


def format_ref(wire_idx, negated):
    """Format a Lean Ref term using the mkRef smart constructor."""
    neg_str = "true" if negated else "false"
    return f"mkRef {wire_idx} {neg_str}"


def format_lit(wire_idx, negated):
    """Format a wire literal inside `gates![...]`: `i` or `¬i`."""
    return f"\u00ac{wire_idx}" if negated else f"{wire_idx}"


def format_circuit(n, num_gates, gates, output_ref):
    """Format a complete Lean Circuit term: ⟨gates![...], mkRef ...⟩.

    Each gate is rendered as `lit ∧ lit`. If there are at most 4 gates the
    list is on one line; otherwise each gate goes on its own line, aligned
    with the first character after `gates![`.
    """
    gate_strs = [
        f"{format_lit(r0[0], r0[1])} \u2227 {format_lit(r1[0], r1[1])}"
        for r0, r1 in gates
    ]
    out = format_ref(output_ref[0], output_ref[1])

    if len(gate_strs) <= 4:
        body = ", ".join(gate_strs)
        return f"\u27e8gates![{body}], {out}\u27e9"
    else:
        # Indent matches the column after `gates![` in the standard layout
        # `  ⟨⟨gates![` (2 spaces + 2 ⟨ + 7 chars `gates![`) → column 11.
        indent = " " * 11
        body = (",\n" + indent).join(gate_strs)
        return f"\u27e8gates![{body}], {out}\u27e9"


def gen_lean_upper_bound(n, batch, func_idx, num_gates, circuit_term):
    """Generate Lean definitions for one function's upper bound."""
    ns = f"Size{n}.Defs{batch}"
    lines = []
    lines.append(f"-- f_{func_idx}: truth table 0x{func_idx:x} \u2014 size {num_gates}")
    lines.append(f"")
    lines.append(f"def f_{func_idx}_size : Nat := {num_gates}")
    lines.append(f"")
    lines.append(f"def f_{func_idx}_upper : HasCircuitOfSize {ns}.f_{func_idx} {num_gates} :=")
    lines.append(f"  \u27e8{circuit_term},")
    lines.append(f"   by circuit_eval\u27e9")
    return "\n".join(lines)


def gen_lean_lower_bound_stub(n, batch, func_idx, num_gates):
    """Generate a sorry'd lower bound stub."""
    ns = f"Size{n}.Defs{batch}"
    lines = []
    lines.append(
        f"def f_{func_idx}_lower : ∀ j, j < {num_gates} → ¬HasCircuitOfSize {ns}.f_{func_idx} j := by"
    )
    lines.append(f"  sorry")
    return "\n".join(lines)


def gen_lean_proofs_file(n, batch, func_indices, results):
    """Generate a complete Proofs file for one batch."""
    lines = []
    lines.append("import Std.Tactic.BVDecide")
    lines.append("import Circuits.Basic")
    lines.append(f"import Size{n}.Defs{batch}")
    lines.append("")
    lines.append(f"namespace Size{n}.Proofs{batch}")
    lines.append("")
    lines.append("open Circuits")
    lines.append("")

    for idx in func_indices:
        if idx in results:
            num_gates, circuit_term = results[idx]
            lines.append(gen_lean_upper_bound(n, batch, idx, num_gates, circuit_term))
            lines.append("")
            lines.append(gen_lean_lower_bound_stub(n, batch, idx, num_gates))
        else:
            lines.append(f"-- f_{idx}: ABC minimization failed")
            lines.append(f"")
            lines.append(f"def f_{idx}_size : Nat := sorry")
            lines.append(f"")
            lines.append(
                f"def f_{idx}_upper : HasCircuitOfSize Size{n}.Defs{batch}.f_{idx} f_{idx}_size := sorry"
            )
            lines.append(f"")
            lines.append(
                f"def f_{idx}_lower : ∀ j, j < f_{idx}_size → ¬HasCircuitOfSize Size{n}.Defs{batch}.f_{idx} j := sorry"
            )
        lines.append("")

    lines.append(f"end Size{n}.Proofs{batch}")
    lines.append("")
    return "\n".join(lines)


# ================================================================
# Main
# ================================================================


def main():
    parser = argparse.ArgumentParser(
        description="Find AIG upper bounds using ABC and emit Lean proof terms"
    )
    parser.add_argument("sizes", type=int, nargs="+", help="Input sizes n")
    parser.add_argument(
        "--func",
        type=int,
        action="append",
        default=None,
        help="Specific function index (can repeat). If omitted, all representatives.",
    )
    parser.add_argument(
        "--write",
        action="store_true",
        help="Write Proofs files to Size{n}/ directories",
    )
    parser.add_argument(
        "--no-exact",
        action="store_true",
        help="Skip SAT-based exact synthesis (faster but may miss optimizations)",
    )
    parser.add_argument("--abc-path", type=str, default=None, help="Path to ABC binary")
    parser.add_argument(
        "--batch-size",
        type=int,
        default=16,
        help="Representatives per batch (default: 16, must match generate.py)",
    )
    args = parser.parse_args()

    abc = find_abc(args.abc_path)
    if abc is None:
        print(
            "Error: ABC not found. Install with: apt install yosys-abc",
            file=sys.stderr,
        )
        print(
            "  Or build from source: https://github.com/berkeley-abc/abc",
            file=sys.stderr,
        )
        sys.exit(1)

    print(f"Using ABC: {abc}", file=sys.stderr)

    for n in args.sizes:
        print(f"\n{'='*60}", file=sys.stderr)
        print(f"Processing n={n}", file=sys.stderr)
        print(f"{'='*60}", file=sys.stderr)

        reps, _ = compute_representatives(n)
        print(
            f"  {num_functions(n)} functions, {len(reps)} representatives",
            file=sys.stderr,
        )

        # Filter to specific functions if requested
        if args.func is not None:
            target_set = set(args.func)
            reps = [r for r in reps if r in target_set]
            if not reps:
                print(f"  No matching representatives for --func {args.func}", file=sys.stderr)
                continue

        # Group into batches (must match generate.py's batch structure)
        all_reps, _ = compute_representatives(n)
        batch_size = min(args.batch_size, len(all_reps))
        num_batches = math.ceil(len(all_reps) / batch_size)

        # Map each representative to its batch
        func_to_batch = {}
        batches = {}
        for batch in range(num_batches):
            start = batch * batch_size
            end = min(start + batch_size, len(all_reps))
            batch_funcs = all_reps[start:end]
            batches[batch] = batch_funcs
            for idx in batch_funcs:
                func_to_batch[idx] = batch

        # Minimize each function
        results_by_batch = {}  # batch -> {func_idx -> (num_gates, circuit_term)}
        target_set = set(reps)

        for idx in reps:
            batch = func_to_batch[idx]
            if batch not in results_by_batch:
                results_by_batch[batch] = {}

            print(f"  f_{idx} (batch {batch})...", end=" ", file=sys.stderr, flush=True)

            result = minimize_aig(abc, n, idx, use_exact=not args.no_exact)
            if result is None:
                print("FAILED", file=sys.stderr)
                continue

            n_inputs, ands, output_lit, input_map = result
            num_gates = len(ands)

            lean_result = aig_to_lean(n, n_inputs, ands, output_lit, input_map)
            if lean_result is None:
                print("FAILED (Lean conversion)", file=sys.stderr)
                continue

            lean_gates, circuit_term = lean_result
            results_by_batch[batch][idx] = (lean_gates, circuit_term)
            print(f"size {lean_gates}", file=sys.stderr)

        # Output results
        for batch in sorted(results_by_batch.keys()):
            batch_funcs = batches[batch]
            # Only include functions from this batch that were targeted
            target_funcs = [f for f in batch_funcs if f in target_set]
            results = results_by_batch[batch]

            if args.write:
                # Write full Proofs file (includes all batch functions)
                content = gen_lean_proofs_file(n, batch, batch_funcs, results)
                path = os.path.join(f"Size{n}", f"Proofs{batch}.lean")
                os.makedirs(f"Size{n}", exist_ok=True)
                with open(path, "w") as f:
                    f.write(content)
                print(f"\n  Wrote {path}", file=sys.stderr)
            else:
                # Print individual upper bound terms to stdout
                for idx in target_funcs:
                    if idx in results:
                        num_gates, circuit_term = results[idx]
                        batch_idx = func_to_batch[idx]
                        print()
                        print(
                            gen_lean_upper_bound(
                                n, batch_idx, idx, num_gates, circuit_term
                            )
                        )
                    else:
                        print(f"\n-- f_{idx}: minimization failed")

        # Summary
        total_found = sum(len(r) for r in results_by_batch.values())
        total_target = len(reps)
        print(f"\n  Summary: {total_found}/{total_target} upper bounds found", file=sys.stderr)

        if total_found > 0:
            all_sizes = []
            for results in results_by_batch.values():
                for idx, (ng, _) in sorted(results.items()):
                    all_sizes.append((idx, ng))
            print(f"\n  {'idx':>6}  {'size':>4}", file=sys.stderr)
            print(f"  {'---':>6}  {'----':>4}", file=sys.stderr)
            for idx, ng in all_sizes:
                print(f"  {idx:>6}  {ng:>4}", file=sys.stderr)


if __name__ == "__main__":
    main()
