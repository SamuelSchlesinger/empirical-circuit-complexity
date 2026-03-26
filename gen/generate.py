#!/usr/bin/env python3
"""
Generate Lean 4 files for the empirical circuit complexity project.

For each input size n, this script generates files only for representative
functions — one per equivalence class under the symmetry group that preserves
circuit complexity. This group combines:
  - S_n: permutation of input variables
  - Z_2^n: negation of individual input variables
  - Z_2: negation of the output
The full group has order 2^{n+1} * n!. Since all these operations correspond
to free transformations on circuits (relabelling/negating wires), every
function in an orbit has the same circuit complexity.

For each n, generates:
  - Size{n}/Defs{m}.lean       : Truth table definitions for representatives
  - Size{n}/Statements{m}.lean : Circuit complexity theorem statements

Convention: Function f_{idx} has truth table encoded by idx.
  Bit j of idx gives f(input_j), where input_j interprets
  (x_0, ..., x_{n-1}) as x_0*2^0 + x_1*2^1 + ... + x_{n-1}*2^{n-1}.

Usage:
  python gen/generate.py 1 2 3
  python gen/generate.py --batch-size 8 3
"""

import argparse
import os
import math
from itertools import permutations


def num_functions(n):
    """Number of Boolean functions {0,1}^n -> {0,1}."""
    return 2 ** (2 ** n)


def truth_value(func_idx, input_idx):
    """Get f_{func_idx}(input_{input_idx}). Bit input_idx of func_idx."""
    return (func_idx >> input_idx) & 1


# ============================================================
# Equivalence classes under S_n × Z_2^n × Z_2
# ============================================================

def apply_perm_to_input_idx(perm, j, n):
    """Given permutation perm on {0,...,n-1} and truth table input index j,
    compute the permuted input index j'.

    If g(x) = f(x ∘ σ) where σ = perm, then g's output at input j equals
    f's output at input j', where j' re-indexes the bits of j by σ."""
    j_prime = 0
    for i in range(n):
        bit = (j >> perm[i]) & 1
        j_prime |= bit << i
    return j_prime


def apply_perm_to_func(perm, func_idx, n):
    """Compute the function index of g where g(x) = f(x ∘ σ)."""
    num_inputs = 1 << n
    new_idx = 0
    for j in range(num_inputs):
        j_prime = apply_perm_to_input_idx(perm, j, n)
        bit = (func_idx >> j_prime) & 1
        new_idx |= bit << j
    return new_idx


def apply_input_negation(func_idx, neg_mask, n):
    """Apply input variable negation to a function.

    neg_mask is a bitmask: if bit i is set, negate input variable x_i.
    On the truth table: output at input j equals original output at j XOR neg_mask."""
    num_inputs = 1 << n
    new_idx = 0
    for j in range(num_inputs):
        j_prime = j ^ neg_mask
        bit = (func_idx >> j_prime) & 1
        new_idx |= bit << j
    return new_idx


def compute_representatives(n):
    """Compute representative function indices under S_n × Z_2^n × Z_2.

    The symmetry group combines input permutation (S_n), individual input
    negation (Z_2^n), and output negation (Z_2). The representative of
    each equivalence class is the minimum index in the orbit.
    Returns a sorted list of representative indices and
    a dict mapping every function index to its representative."""
    total = num_functions(n)
    output_neg_mask = total - 1  # XOR with this flips all truth table bits
    rep_of = {}

    for func_idx in range(total):
        if func_idx in rep_of:
            continue
        # Compute orbit under full symmetry group
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


# ============================================================
# Lean code generation
# ============================================================

def gen_if_tree(n, func_idx, var=0, input_acc=0, indent=1):
    """Generate nested if-then-else tree for the truth table."""
    if var == n:
        return "true" if truth_value(func_idx, input_acc) else "false"

    inner = "  " * (indent + 1)
    prefix = "  " * indent

    then_body = gen_if_tree(n, func_idx, var + 1,
                            input_acc | (1 << var), indent + 1)
    else_body = gen_if_tree(n, func_idx, var + 1,
                            input_acc, indent + 1)

    return (f"if x \u27e8{var}, by omega\u27e9 then\n"
            f"{inner}{then_body}\n"
            f"{prefix}else\n"
            f"{inner}{else_body}")


def gen_defs(n, batch_idx, func_indices):
    """Generate a Defs file for the given representative functions."""
    lines = []
    lines.append("import Circuits.Basic")
    lines.append("")
    lines.append(f"namespace Size{n}.Defs{batch_idx}")
    lines.append("")

    for idx in func_indices:
        body = gen_if_tree(n, idx)
        lines.append(f"def f_{idx} (x : Fin {n} \u2192 Bool) : Bool :=")
        lines.append(f"  {body}")
        lines.append("")

    lines.append(f"end Size{n}.Defs{batch_idx}")
    lines.append("")
    return "\n".join(lines)


def gen_statements(n, batch_idx, func_indices):
    """Generate a Statements file for the given representative functions."""
    defs_ns = f"Size{n}.Defs{batch_idx}"
    proofs_ns = f"Size{n}.Proofs{batch_idx}"

    lines = []
    lines.append("import Circuits.Basic")
    lines.append(f"import Size{n}.Defs{batch_idx}")
    lines.append(f"import Size{n}.Proofs{batch_idx}")
    lines.append("")
    lines.append("/-")
    lines.append(f"  Circuit complexity theorems for {len(func_indices)} representative functions")
    lines.append(f"  of {n} input variable(s) (batch {batch_idx}).")
    lines.append("")
    lines.append(f"  Each theorem references proof terms from {proofs_ns},")
    lines.append(f"  which must provide for each representative function index idx:")
    lines.append(f"    f_{{idx}}_size  : Nat")
    lines.append(f"    f_{{idx}}_upper : Circuits.HasCircuitOfSize {defs_ns}.f_{{idx}} f_{{idx}}_size")
    lines.append(f"    f_{{idx}}_lower : \u2200 j, j < f_{{idx}}_size \u2192")
    lines.append(f"                      \u00ac Circuits.HasCircuitOfSize {defs_ns}.f_{{idx}} j")
    lines.append("-/")
    lines.append("")
    lines.append(f"namespace Size{n}.Statements{batch_idx}")
    lines.append("")

    for idx in func_indices:
        lines.append(f"theorem f_{idx}_complexity :")
        lines.append(f"    Circuits.CircuitComplexity {defs_ns}.f_{idx} {proofs_ns}.f_{idx}_size :=")
        lines.append(f"  \u27e8{proofs_ns}.f_{idx}_upper, {proofs_ns}.f_{idx}_lower\u27e9")
        lines.append("")

    lines.append(f"end Size{n}.Statements{batch_idx}")
    lines.append("")
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(
        description="Generate Lean 4 files for empirical circuit complexity"
    )
    parser.add_argument("sizes", type=int, nargs="+",
                        help="Input sizes n to generate for")
    parser.add_argument("--batch-size", type=int, default=16,
                        help="Representatives per batch (default: 16)")
    args = parser.parse_args()

    for n in args.sizes:
        total = num_functions(n)

        print(f"Computing equivalence classes for n={n}...")
        reps, rep_of = compute_representatives(n)
        print(f"  {total} functions, {len(reps)} representatives "
              f"({total - len(reps)} derived by symmetry)")

        dir_name = f"Size{n}"
        os.makedirs(dir_name, exist_ok=True)

        batch_size = min(args.batch_size, len(reps))
        num_batches = math.ceil(len(reps) / batch_size)

        for batch in range(num_batches):
            start = batch * batch_size
            end = min(start + batch_size, len(reps))
            func_indices = reps[start:end]

            defs_path = os.path.join(dir_name, f"Defs{batch}.lean")
            with open(defs_path, "w") as f:
                f.write(gen_defs(n, batch, func_indices))
            print(f"  {defs_path} ({len(func_indices)} functions)")

            stmts_path = os.path.join(dir_name, f"Statements{batch}.lean")
            with open(stmts_path, "w") as f:
                f.write(gen_statements(n, batch, func_indices))
            print(f"  {stmts_path}")

        print(f"Size {n}: {len(reps)} representatives in {num_batches} batch(es)")
        print()


if __name__ == "__main__":
    main()
