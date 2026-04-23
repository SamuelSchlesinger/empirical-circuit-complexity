# Lower Bound Patterns

A lower bound proof shows that no circuit of size less than k computes the
function. This is the hard direction — it requires ruling out all possible
circuits.

## Pattern: Size-1 functions — `hasSize0_iff` + `decide`

For a function known to have circuit complexity 1, the lower bound goal is
`∀ j, j < 1 → ¬HasCircuitOfSize f j`. The single non-vacuous case is `j = 0`.
The lemma `hasSize0_iff` characterizes size-0 circuits as exactly the
wire-or-negated-wire functions, and the `decForallFinBool` instance makes
the resulting statement decidable:

```lean
def f_0_lower : ∀ j, j < 1 → ¬HasCircuitOfSize Foo.f_0 j := by
  intro j hj
  obtain rfl : j = 0 := by omega
  rw [hasSize0_iff]; decide
```

Supporting machinery in `Circuits/Basic.lean`:

- `hasSize0_iff : HasCircuitOfSize f 0 ↔ ∃ idx neg, ∀ x, f x = (if neg then !x idx else x idx)`
- `decForallFinBool` — `Decidable (∀ x : Fin n → Bool, p x)` via `allBool` enumeration.
- `allBool` / `consFn` / `allBool_eq_true` — Bool-valued enumeration over `2^n` inputs.

`decide` evaluates `allBool` in the kernel; cost is `O(2^n)` per `(idx, neg)` pair.

## Pattern: Vacuous Lower Bound

When the complexity is 0, the goal `∀ j, j < 0 → …` is vacuously true:

```lean
def f_idx_lower : ∀ j, j < 0 → ¬HasCircuitOfSize Foo.f_idx j :=
  fun _ h => absurd h (by omega)
```

## Pattern: Constant Functions Have No Size-0 Circuit (specialized)

`Circuits.no_size0_of_constant` is a hand-written lemma that predates the
generic `hasSize0_iff` decision procedure. It still works and is occasionally
useful when n is large (the kernel `decide` cost is `O(2^n)`, so the generic
approach doesn't scale beyond ≈ 6 inputs).

```lean
theorem no_size0_of_constant {n : Nat} {f : (Fin n → Bool) → Bool}
    (hf : f (fun _ => true) = f (fun _ => false)) :
    ¬HasCircuitOfSize f 0
```

## Scaling Considerations

For n ≤ 5 or so, the `rw [hasSize0_iff]; decide` pattern is fully automatic.
Beyond that, kernel evaluation gets slow and we'll need:
- `no_size0_of_constant` for constant functions
- Hand-written counterexamples for the wire-and-negation cases
- For size ≥ 2, structural arguments (Shannon decomposition, fan-in analysis,
  etc.) since exhaustive circuit enumeration explodes combinatorially

## Pattern: Input Minors

`Circuits.noCircuitOfSize_of_inputMinor` transfers a lower bound from a hard
minor. If substituting literals for the inputs of `f` yields `g`, then any
size-`k` circuit for `f` would give a size-`k` circuit for `g`.

This closes representatives like `Size3.f_27` and `Size3.f_60`, which contain
the 2-input XOR representative as a literal minor.

## Pattern: Last-Gate Decomposition

`Circuits.HasCircuitOfSize.succ_decompose` exposes the final gate of a circuit.
A `(k+1)`-gate circuit either ignores its last gate, or computes an AND/NAND of
two functions already computable by the `k`-gate prefix.

The contrapositive helper is:

```lean
noCircuitOfSize_succ_of_no_decompose
```

This is the intended next step for the hard Size3 lower bounds: prove that the
two prefix functions needed for the target cannot coexist in the same smaller
prefix, instead of enumerating all size-3 circuits directly.

