# Upper Bound Patterns

An upper bound proof exhibits a concrete circuit and proves it computes the
target function.

## Pattern: Smart Constructors + `circuit_eval`

`Circuits/Basic.lean` exports four helpers that make upper-bound proofs nearly
mechanical:

- `mkRef i neg` — build a `Ref b` at index `i` with negation bit `neg`. The
  bound `i < b` is auto-discharged by `omega`.
- `mkGate li ln ri rn` — build an AND `Gate b` with left/right index/negation
  pairs. Both bounds auto-discharged by `omega`.
- `gates![g₀, g₁, …, gₘ]` — list-style notation for a `GateList`. Each gate
  is written as `lit ∧ lit` where each literal is either `i` (positive wire)
  or `¬i` / `!i` (negated wire). Gates appear in execution (topological)
  order: `g₀` is the first gate executed, available at wire index `n` (where
  `n` is the input arity).
- `circuit_eval` — tactic that unfolds circuit evaluation, normalizes the
  `Nat.add n k` bound expressions arising from the dependent `GateList`
  index, and discharges the remaining Boolean equation with `bv_decide`.
  By default, the head constant of the goal's right-hand side is the
  function definition that gets unfolded; pass `circuit_eval Foo.f_idx`
  to override.

### Standard form

```lean
def f_idx_upper : HasCircuitOfSize Foo.f_idx s :=
  ⟨⟨gates![¬1 ∧ 0, ¬3 ∧ ¬2, …], mkRef out outNeg⟩,
   by circuit_eval⟩
```

Each `lit ∧ lit` denotes an AND gate; `¬i` flips the input wire. Reading the
list left-to-right gives execution order — the `k`-th gate is available at
wire `n + k`.

### Wire-only circuits (size 0)

When a function equals a single input variable (possibly negated), pass an
empty gate list:

```lean
⟨⟨gates![], mkRef i neg⟩, by circuit_eval⟩
```

### Constant-producing circuits (size 1)

To produce a constant we need at least one gate. The standard idiom is
`AND(xᵢ, ¬xᵢ) = false`, optionally negating the output for `true`:

```lean
-- Constant false: AND(x₀, ¬x₀), output = gate 0
⟨gates![0 ∧ ¬0], mkRef n false⟩

-- Constant true: same gate, output = ¬(gate 0)
⟨gates![0 ∧ ¬0], mkRef n true⟩
```

(Here `n` is the input arity; the gate lives at wire `n`.)

## Why `circuit_eval` works

The dependent `GateList` index uses `Nat.add` (e.g. `extendEnv : (Fin (n+k) → Bool) → … → Fin (Nat.add n k + 1) → Bool`). Lean's default simprocs only
normalize `HAdd.hAdd`, leaving `Nat.add 3 5` untouched. The macro inserts a
single rewrite `∀ a b, Nat.add a b = a + b` (proved by `rfl`) which converts
these to `+`, after which `Nat.reduceAdd` reduces them to literals. The
resulting Boolean equation is closed by `bv_decide`.

## Where it appears

- **Size 1**: `Size1/Proofs0.lean` (f_0 const, f_1 negated wire)
- **Size 2**: `Size2/Proofs0.lean` (4 representatives)
- **Size 3**: `Size3/Proofs0.lean` (14 representatives)
