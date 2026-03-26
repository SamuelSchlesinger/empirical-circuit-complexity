# Lower Bound Patterns

A lower bound proof shows that no circuit of size less than k computes the
function. This is the hard direction — it requires ruling out all possible
circuits.

## Pattern: Constant Functions Have No Size-0 Circuit

This is proved as a general lemma `Circuits.no_size0_of_constant` in
`Circuits/Basic.lean`. It works for any number of inputs n:

```lean
theorem no_size0_of_constant {n : Nat} {f : (Fin n → Bool) → Bool}
    (hf : f (fun _ => true) = f (fun _ => false)) :
    ¬HasCircuitOfSize f 0
```

The key insight: constant inputs (`fun _ => true` and `fun _ => false`) make the
circuit output depend only on the negation bit, not which wire is referenced.
A size-0 circuit always gives different outputs on these two inputs, but a
constant function gives the same output. Contradiction.

To apply it, just prove the function is constant on all-true vs all-false:

```lean
exact no_size0_of_constant (by simp [<f_def>])
```

### Where it appears

- **Size 1**: `Size1/Proofs0.lean`, f_0_lower and f_3_lower

## Pattern: Exhaustive Case Split (Size 0, non-constant)

For non-constant functions that still need a size-0 lower bound excluded
(because their complexity is > 0 for other reasons), a direct case split
is needed. Destructure the circuit output, pin the Fin index, case-split
on the negation bit, and provide a counterexample input for each case.

This shouldn't arise often — most non-constant functions on small n are
literals (single variable, possibly negated) and DO have size-0 circuits.

## Pattern: Vacuous Lower Bound

When the complexity is 0, the lower bound `∀ j, j < 0 → ...` is vacuously true:

```lean
fun j hj => absurd hj (by omega)
```

### Where it appears

- **Size 1**: `Size1/Proofs0.lean`, f_1_lower and f_2_lower

## Scaling Considerations

For n=2 and beyond, size-0 lower bounds require handling `Fin 2` (or larger)
indices — more cases to split. For size-1 lower bounds, we must enumerate all
possible gates (each input to the gate is a `Ref n` with 2n choices), which
grows as O(n²) circuits. For size ≥ 2, the enumeration grows further.

Potential approaches for larger lower bounds:
- Factor the proof by first reducing to canonical forms
- Use Shannon decomposition: fix one variable and appeal to smaller-n results
- Batch cases that share the same counterexample input
