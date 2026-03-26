# Empirical Circuit Complexity

The research program in this document is to empirically prove the circuit
complexity of concrete functions {0, 1}^n -> {0, 1} for small n. This will
proceed as follows:

First, we will define a type of Boolean circuits. A circuit is a DAG of fan-in 2
AND gates, where each wire (input to a gate or the circuit output) can be
optionally negated at zero cost. NOT is not a gate — it is simply a bit on a
wire that flips the signal. Circuit size is defined as the number of AND gates.

All proofs in this project must be explicit. We do not use `native_decide` or
other opaque decision procedures. The goal is to produce transparent,
human-reviewable proof terms.

Then, we will begin at n = 1 and proceed on the following task, incrementing n
as we continue. For each n, three kinds of files are produced, with a clear
trust boundary between them:

1. `Size<n>/Defs<m>.lean` — Generated programmatically by a program we review
   and trust. Contains the tabular representations of Boolean functions, encoded
   as Lean 4 functions `(Fin n → Bool) → Bool`. If batched, m indexes the batch.

2. `Size<n>/Proofs<m>.lean` — Written by AI. Contains the actual proof terms:
   upper bounds (exhibiting concrete circuits) and lower bounds (ruling out
   smaller circuits). These are the only files AI touches directly.

3. `Size<n>/Statements<m>.lean` — Generated programmatically by the same trusted
   program. Imports both the Defs and Proofs modules, and states the circuit
   complexity theorems, drawing the proof terms from the Proofs module.

This separation means we trust only the generator program (which we review) and
Lean's type checker. If any AI-generated proof is wrong, the project simply does
not compile. The Statements files are the source of truth for what is being
claimed; the Proofs files merely supply evidence that Lean verifies.

Proofs may depend on other proofs, including proofs for smaller n. This enables
recursive proof structures — for instance, a proof for a 3-input function might
fix one variable and appeal to already-proven complexity results for the
resulting 2-input subfunctions. This compositional approach mirrors Shannon
decomposition and may reveal interesting recursive structure in circuit
complexity as n grows.

Constants (the always-0 and always-1 functions) are not free — they cost one
gate (e.g., AND(x, NOT(x)) = FALSE).

## Symmetry group

Three operations on circuits preserve size and are therefore free:

1. **Input permutation** (S_n): relabel input wires. Proved as
   `Circuits.CircuitComplexity_perm`.
2. **Input negation** (Z_2^n): flip the negation bit on any input wire. Proved
   as `Circuits.CircuitComplexity_negInput`.
3. **Output negation** (Z_2): flip the negation bit on the output wire. Proved
   as `Circuits.CircuitComplexity_neg`.

These generate a symmetry group of order 2^{n+1} · n! acting on
Boolean functions. The generator groups functions into equivalence classes
under this full group. Only one representative per class needs a direct proof;
the remaining functions derive their complexity via the invariance theorems.

| n | Total      | Representatives | Reduction |
|---|------------|-----------------|-----------|
| 1 | 4          | 2               | 2x        |
| 2 | 16         | 4               | 4x        |
| 3 | 256        | 14              | 18x       |
| 4 | 65,536     | 222             | 295x      |
| 5 | ~4.3 × 10⁹ | 616,126        | 6,971x    |

## Truth table encoding

Function `f_idx` has its truth table encoded by `idx`: bit `j` of `idx` gives
`f(input_j)`, where `input_j` interprets `(x_0, ..., x_{n-1})` in little-endian
binary as `x_0 * 2^0 + x_1 * 2^1 + ... + x_{n-1} * 2^{n-1}`. For example, with
n = 2, function index 6 (binary 0110) maps inputs (0,0)→0, (1,0)→1, (0,1)→1,
(1,1)→0 — this is XOR.

## Generator

The trusted generator lives at `gen/generate.py`. Usage:

```
python gen/generate.py 1 2 3              # generate for n = 1, 2, 3
python gen/generate.py --batch-size 8 3   # custom batch size
```

The default batch size is 16 functions per file.

## Proof contract

Each `Size<n>/Proofs<m>.lean` file must export, for every **representative**
function index `idx` in its batch:

- `f_{idx}_size  : Nat` — the circuit complexity
- `f_{idx}_upper : Circuits.HasCircuitOfSize f_{idx} f_{idx}_size` — a witness circuit
- `f_{idx}_lower : ∀ j, j < f_{idx}_size → ¬Circuits.HasCircuitOfSize f_{idx} j` — optimality

The generated Statements file combines these into a `Circuits.CircuitComplexity`
theorem for each function.

## Dependencies

This project uses Lean 4 (v4.28.0) with no external dependencies — no Mathlib
or other libraries. This is a deliberate choice, though we are open to
reconsidering if the proofs call for it.

## Patterns

The `patterns/` directory documents proof patterns and structural observations
as they emerge from the work:

- `patterns/upper-bounds.md` — how upper bound proofs are constructed
- `patterns/lower-bounds.md` — how lower bound proofs are structured, including
  counterexample selection and scaling considerations
- `patterns/observations.md` — results tables and structural observations (e.g.,
  negation symmetry, constant function costs, proof technique notes)

This is a living record of what we learn as we push through increasing n.

## Target

The initial target is to complete this for n = 1 through n = 4, covering
4 + 16 + 256 + 65,536 = 65,812 functions total (2 + 4 + 14 + 222 = 242
representative proofs needed).

By doing so, we will be gaining knowledge on how to prove circuit lower bounds
not for families of circuits, but for concrete circuits. Hopefully, this
knowledge will translate into interesting insights into how we could proceed
with general purpose circuit lower bounds in the future.
