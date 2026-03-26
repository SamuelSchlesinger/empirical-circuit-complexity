Read the README.md for full context on this project — its goals, architecture,
trust model, conventions, and proof contract.

Read the `patterns/` directory for documented proof patterns, observations, and
technique notes that have emerged from the work so far.

## Current state

- **Size1**: Complete. Both 2 representatives proven in `Size1/Proofs0.lean`.
- **Size2**: Defs and Statements generated for 4 representatives. Proofs needed.
- **Size3**: Defs and Statements generated for 14 representatives. Proofs needed.
- **Size4**: Not yet generated. Run `python3 gen/generate.py 4` (222 representatives).

## Key conventions

- **No `native_decide`**. Proofs must be explicit and human-reviewable.
- **Representatives only**: The generator (`gen/generate.py`) emits files only for
  one representative per equivalence class under the full symmetry group
  (S_n input permutation × Z_2^n input negation × Z_2 output negation).
  Non-representative functions are omitted entirely.
- **Proof file contract**: Each `Size{n}/Proofs{m}.lean` exports `f_{idx}_size`,
  `f_{idx}_upper`, and `f_{idx}_lower` for each representative in the batch.
  Use concrete numbers (not `f_{idx}_size`) in the types of `_upper` and `_lower`
  because `omega` cannot see through definitions.
- **simp for evaluation**: `simp [Circuit.eval, Ref.eval, GateList.eval, Gate.eval,
  extendEnv, <function_def>]` is the standard way to evaluate concrete circuits.
- **simp loops on free variables**: Always case-split on the negation bit (and Fin
  index if needed) BEFORE running simp on circuit evaluations. simp diverges on
  `if neg then ... else ...` when `neg` is a free variable.

## Building

- `lake build` — builds just the Circuits library (definitions + lemmas)
- `lake build Size1.Statements0` — builds the full Size1 chain (Defs → Proofs → Statements)
- `lake build Size2.Defs0` — builds Size2 definitions (Proofs don't exist yet)
- After writing `Size{n}/Proofs{m}.lean`, test with `lake build Size{n}.Statements{m}`

## Open sorry

Two eval lemmas in `Circuits/Basic.lean` are sorry'd — both conceptually
straightforward but tedious due to dependent types in `GateList`:

- `Circuit.eval_permuteInputs` — evaluating a permuted circuit equals evaluating
  the original on permuted input. `CircuitComplexity_perm` depends on it.
- `Circuit.eval_negateInput` — evaluating a circuit with a negated input wire
  equals evaluating the original with that input flipped. `CircuitComplexity_negInput`
  depends on it.

The output negation theorem (`CircuitComplexity_neg`) is fully proved — no sorry —
because it only flips a single bit on the output reference.

None of these are used by any generated code currently.

## Before pushing

Regenerate the paper PDF before pushing:
```
cd paper && pdflatex -interaction=nonstopmode main.tex && pdflatex -interaction=nonstopmode main.tex && cd ..
```
The PDF is checked into the repo so readers can view it directly on GitHub.
