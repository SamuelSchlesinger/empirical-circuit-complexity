# Upper Bound Patterns

An upper bound proof exhibits a concrete circuit and proves it computes the
target function.

## Pattern: Witness Circuit + Simp

Construct a `Circuit n k` term and prove `computes` via:

```lean
fun input => by
  simp [Circuit.eval, Ref.eval, GateList.eval, Gate.eval, extendEnv, <function_def>]
```

`simp` unfolds the circuit evaluation, the function definition, and closes the
goal by reducing both sides to the same Bool expression for all inputs.

This works because:
- The circuit is a concrete term (no variables), so all gate evaluations reduce.
- The function definition is an if-then-else tree, which also fully reduces.
- `simp` handles Bool identities like `a && !a = false` and `if true/false`
  simplification.

### Where it appears

- **Size 1, all functions**: `Size1/Proofs0.lean`
  - f_0 (constant false): 1-gate circuit AND(x₀, ¬x₀) with output = gate 0
  - f_1 (¬x₀): 0-gate circuit with negated wire
  - f_2 (x₀): 0-gate circuit with direct wire
  - f_3 (constant true): 1-gate circuit AND(x₀, ¬x₀) with negated output

### Wire-Only Circuits (Size 0)

When a function equals a single input variable (possibly negated), the circuit
has 0 gates — just a `Ref` pointing to the right input wire with the right
negation bit. The anonymous constructor is compact:

```lean
⟨⟨.nil, ⟨⟨i, by omega⟩, neg⟩⟩, fun input => by simp [...]⟩
```

### Constant-Producing Circuits (Size 1)

To produce a constant output, we need at least 1 gate since there are no free
constant wires. The standard idiom is AND(xᵢ, ¬xᵢ) = false, then optionally
negate the output for true:

```lean
-- Constant false: AND(x₀, ¬x₀), output = gate 0
⟨.cons .nil ⟨⟨⟨0, by omega⟩, false⟩, ⟨⟨0, by omega⟩, true⟩⟩, ⟨⟨1, by omega⟩, false⟩⟩

-- Constant true: same gate, output = ¬(gate 0)
⟨.cons .nil ⟨⟨⟨0, by omega⟩, false⟩, ⟨⟨0, by omega⟩, true⟩⟩, ⟨⟨1, by omega⟩, true⟩⟩
```
