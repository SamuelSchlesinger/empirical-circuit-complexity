# Observations

Structural observations from the circuit complexity results so far.

## Size 1 (n=1): 4 functions, 2 representatives

| idx | Function    | Complexity | Notes                          |
|-----|-------------|------------|--------------------------------|
| 0   | constant 0  | 1          | AND(x₀, ¬x₀)                  |
| 1   | ¬x₀         | 0          | negation is free               |

Non-representatives: f_2 (x₀) = output negation of f_1; f_3 (constant 1) = output
negation of f_0.

### Key takeaways

- **Negation is free**: f_1 (¬x₀) has complexity 0, confirming that our circuit
  model correctly treats NOT as a zero-cost wire annotation.

- **Constants cost 1 gate**: This is a consequence of having no free constant wires.
  The cheapest way to produce a constant is AND(x, ¬x) = false (1 gate).

- **Full symmetry group**: The equivalence classes under S_n × Z_2^n × Z_2 capture
  all free circuit transformations: input permutation, input negation, and output
  negation. A function and its complement always have the same complexity (output
  negation). A function and its input-negated variant always have the same
  complexity (input negation).

## Proof Technique Notes

- **omega opacity**: `omega` does not unfold definitions, even `@[reducible]` ones.
  The `f_X_size` definitions are opaque to omega. Fix: use concrete numbers in
  the `_upper` and `_lower` type signatures; the Statements file still works
  because the types match definitionally.

- **simp power**: `simp` with the evaluation definitions (`Circuit.eval`,
  `Ref.eval`, `GateList.eval`, `Gate.eval`, `extendEnv`) is sufficient to fully
  evaluate concrete circuits on symbolic inputs and close both upper bound proofs
  and lower bound contradictions. It handles Bool identities, if-then-else
  reduction, and beta reduction in one pass.
