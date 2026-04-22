/-
  Boolean circuit definitions for empirical circuit complexity.

  A circuit is a DAG of fan-in 2 AND gates, where each wire can be
  optionally negated at zero cost. Circuit size = number of AND gates.
-/
import Std.Tactic.BVDecide
import Lean.Elab.Tactic

namespace Circuits

/-- Extend a wire environment with one additional wire value. -/
def extendEnv {n : Nat} (env : Fin n → Bool) (val : Bool) : Fin (n + 1) → Bool :=
  fun i => if h : i.val < n then env ⟨i.val, h⟩ else val

/-- A reference to a wire, with optional negation.
    `bound` is the number of available wires. -/
structure Ref (bound : Nat) where
  index : Fin bound
  negated : Bool
  deriving DecidableEq, Repr

/-- Evaluate a wire reference in an environment. -/
def Ref.eval (r : Ref bound) (env : Fin bound → Bool) : Bool :=
  if r.negated then !(env r.index) else env r.index

/-- An AND gate with two wire inputs. -/
structure Gate (bound : Nat) where
  lhs : Ref bound
  rhs : Ref bound
  deriving DecidableEq, Repr

/-- Evaluate a gate in an environment. -/
def Gate.eval (g : Gate bound) (env : Fin bound → Bool) : Bool :=
  g.lhs.eval env && g.rhs.eval env

/-- A sequence of AND gates in topological order.
    Gate i can reference n + i wires: n inputs plus i previous gate outputs. -/
inductive GateList (n : Nat) : Nat → Type where
  | nil : GateList n 0
  | cons : GateList n k → Gate (n + k) → GateList n (k + 1)

/-- Build the full wire environment by evaluating gates in order. -/
def GateList.eval (input : Fin n → Bool) : GateList n k → Fin (n + k) → Bool
  | .nil => input
  | .cons prev gate =>
    let prevEnv := GateList.eval input prev
    extendEnv prevEnv (gate.eval prevEnv)

/-- A Boolean circuit with n inputs and k AND gates. -/
structure Circuit (n : Nat) (k : Nat) where
  gates : GateList n k
  output : Ref (n + k)

/-- Evaluate a circuit on a given input assignment. -/
def Circuit.eval (c : Circuit n k) (input : Fin n → Bool) : Bool :=
  c.output.eval (c.gates.eval input)

/-- A circuit computes a Boolean function. -/
def Circuit.computes (c : Circuit n k) (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ input, c.eval input = f input

/-- There exists a circuit of size k computing f. -/
def HasCircuitOfSize {n : Nat} (f : (Fin n → Bool) → Bool) (k : Nat) : Prop :=
  ∃ c : Circuit n k, c.computes f

/-- The circuit complexity of f is exactly k:
    a size-k circuit computing f exists,
    and no smaller circuit does. -/
def CircuitComplexity {n : Nat} (f : (Fin n → Bool) → Bool) (k : Nat) : Prop :=
  HasCircuitOfSize f k ∧ ∀ j, j < k → ¬HasCircuitOfSize f j

-- ============================================================
-- Input permutation invariance
-- ============================================================

/-- Remap a wire reference through an input permutation.
    Input wires (index < n) are remapped by σ; gate wires are unchanged. -/
def Ref.permuteInputs (r : Ref bound) (n : Nat) (σ : Fin n → Fin n)
    (hn : n ≤ bound) : Ref bound :=
  if h : r.index.val < n then
    ⟨⟨(σ ⟨r.index.val, h⟩).val, by have := (σ ⟨r.index.val, h⟩).isLt; omega⟩, r.negated⟩
  else r

/-- Remap a gate's wire references through an input permutation. -/
def Gate.permuteInputs (g : Gate bound) (n : Nat) (σ : Fin n → Fin n)
    (hn : n ≤ bound) : Gate bound :=
  ⟨g.lhs.permuteInputs n σ hn, g.rhs.permuteInputs n σ hn⟩

/-- Remap all input references in a gate list through a permutation. -/
def GateList.permuteInputs (σ : Fin n → Fin n) : GateList n k → GateList n k
  | .nil => .nil
  | .cons prev gate => .cons (prev.permuteInputs σ) (gate.permuteInputs n σ (by omega))

/-- Remap a circuit's input wires through a permutation. -/
def Circuit.permuteInputs (c : Circuit n k) (σ : Fin n → Fin n) : Circuit n k :=
  ⟨c.gates.permuteInputs σ, c.output.permuteInputs n σ (by omega)⟩

/-- Evaluating a permuted circuit on input x equals evaluating
    the original circuit on x ∘ σ. The permuted gate list produces
    the same gate outputs because each remapped input reference σ(i)
    reads input(σ(i)) from the base environment, which matches what
    the original circuit reads as (input ∘ σ)(i). -/
theorem Circuit.eval_permuteInputs (c : Circuit n k) (σ : Fin n → Fin n)
    (input : Fin n → Bool) :
    (c.permuteInputs σ).eval input = c.eval (input ∘ σ) := by
  sorry -- TODO: induction on gate list with environment invariant

/-- Circuit complexity is invariant under permutation of input variables.
    Given mutually inverse permutations σ and τ, if g(x) = f(x ∘ σ) for all x,
    then f and g have the same circuit complexity. -/
theorem CircuitComplexity_perm {n : Nat} {f g : (Fin n → Bool) → Bool} {k : Nat}
    (σ τ : Fin n → Fin n)
    (hστ : ∀ i, σ (τ i) = i)
    (hτσ : ∀ i, τ (σ i) = i)
    (hfg : ∀ x, g x = f (x ∘ σ)) :
    CircuitComplexity f k → CircuitComplexity g k := by
  intro ⟨⟨c, hc⟩, hlower⟩
  refine ⟨⟨c.permuteInputs σ, fun input => ?_⟩, fun j hj ⟨c', hc'⟩ => ?_⟩
  · -- Upper bound: permuted circuit computes g
    rw [Circuit.eval_permuteInputs, hfg, hc]
  · -- Lower bound: if c' computes g, then c'.permuteInputs τ computes f
    exact hlower j hj ⟨c'.permuteInputs τ, fun input => by
      rw [Circuit.eval_permuteInputs, hc' (input ∘ τ), hfg (input ∘ τ)]
      congr 1; ext i; simp [Function.comp, hτσ]⟩

-- ============================================================
-- Output negation invariance
-- ============================================================

/-- Negate the output of a circuit by flipping the output reference's negation bit. -/
def Circuit.negateOutput (c : Circuit n k) : Circuit n k :=
  ⟨c.gates, ⟨c.output.index, !c.output.negated⟩⟩

/-- Negating a circuit's output negates its evaluation. -/
theorem Circuit.eval_negateOutput (c : Circuit n k) (input : Fin n → Bool) :
    c.negateOutput.eval input = !(c.eval input) := by
  simp [Circuit.negateOutput, Circuit.eval, Ref.eval]
  cases c.output.negated <;> simp

/-- Circuit complexity is invariant under output negation.
    Negating the output wire is free (just flip its negation bit),
    so f and (fun x => !(f x)) always have the same complexity. -/
theorem CircuitComplexity_neg {n : Nat} {f : (Fin n → Bool) → Bool} {k : Nat}
    (hfk : CircuitComplexity f k) :
    CircuitComplexity (fun x => !(f x)) k := by
  obtain ⟨⟨c, hc⟩, hlower⟩ := hfk
  refine ⟨⟨c.negateOutput, fun input => ?_⟩, fun j hj ⟨c', hc'⟩ => ?_⟩
  · rw [Circuit.eval_negateOutput, hc]
  · exact hlower j hj ⟨c'.negateOutput, fun input => by
      rw [Circuit.eval_negateOutput, hc' input]; simp⟩

-- ============================================================
-- Input negation invariance
-- ============================================================

/-- Flip the negation bit on a wire reference if it refers to input wire i.
    Gate wires (index ≥ n) are unchanged. -/
def Ref.negateInput (r : Ref bound) (i : Fin n) (hn : n ≤ bound) : Ref bound :=
  if r.index.val = i.val then ⟨r.index, !r.negated⟩ else r

/-- Negate input wire i in a gate. -/
def Gate.negateInput (g : Gate bound) (i : Fin n) (hn : n ≤ bound) : Gate bound :=
  ⟨g.lhs.negateInput i hn, g.rhs.negateInput i hn⟩

/-- Negate input wire i throughout a gate list. -/
def GateList.negateInput (i : Fin n) : GateList n k → GateList n k
  | .nil => .nil
  | .cons prev gate => .cons (prev.negateInput i) (gate.negateInput i (by omega))

/-- Negate input wire i in a circuit. -/
def Circuit.negateInput (c : Circuit n k) (i : Fin n) : Circuit n k :=
  ⟨c.gates.negateInput i, c.output.negateInput i (by omega)⟩

/-- Evaluating a circuit with negated input wire i on input x equals
    evaluating the original circuit on x with bit i flipped.
    Conceptually straightforward (flip one wire's negation bits) but
    the dependent types in GateList make the induction proof tedious. -/
theorem Circuit.eval_negateInput (c : Circuit n k) (i : Fin n)
    (input : Fin n → Bool) :
    (c.negateInput i).eval input =
    c.eval (fun j => if j = i then !input j else input j) := by
  sorry -- TODO: induction on gate list with environment invariant

/-- Circuit complexity is invariant under negation of an input variable.
    Flipping the negation bit on input wire i is free, so
    f and (fun x => f (fun j => if j = i then !x j else x j))
    always have the same complexity. -/
theorem CircuitComplexity_negInput {n : Nat} {f : (Fin n → Bool) → Bool} {k : Nat}
    (i : Fin n) (hfk : CircuitComplexity f k) :
    CircuitComplexity (fun x => f (fun j => if j = i then !(x j) else x j)) k := by
  obtain ⟨⟨c, hc⟩, hlower⟩ := hfk
  refine ⟨⟨c.negateInput i, fun input => ?_⟩, fun j hj ⟨c', hc'⟩ => ?_⟩
  · rw [Circuit.eval_negateInput, hc]
  · exact hlower j hj ⟨c'.negateInput i, fun input => by
      rw [Circuit.eval_negateInput]
      have h := hc' (fun p => if p = i then !input p else input p)
      rw [h]; dsimp only
      congr 1; funext p
      by_cases hp : p = i <;> simp [hp]⟩

-- ============================================================
-- Size-0 lower bounds
-- ============================================================

/-- A size-0 circuit outputs a single (possibly negated) input wire.
    On constant inputs, the output depends only on the negation bit,
    so no constant function (where f(all-true) = f(all-false)) has a
    size-0 circuit. Works for any number of inputs. -/
theorem no_size0_of_constant {n : Nat} {f : (Fin n → Bool) → Bool}
    (hf : f (fun _ => true) = f (fun _ => false)) :
    ¬HasCircuitOfSize f 0 := by
  intro ⟨⟨gates, ⟨idx, neg⟩⟩, hc⟩
  match gates with
  | .nil =>
    have h₁ := hc (fun _ => true)
    have h₂ := hc (fun _ => false)
    cases neg <;> {
      simp [Circuit.eval, Ref.eval, GateList.eval] at h₁ h₂
      simp_all }

-- ============================================================
-- Decidability of `∀ x : Fin n → Bool, p x` for small n
-- ============================================================

/-- Cons a Boolean value at the head of a `Fin n → Bool` family. -/
def consFn {n : Nat} (b : Bool) (y : Fin n → Bool) : Fin (n+1) → Bool :=
  fun i => if h : i.val = 0 then b else y ⟨i.val - 1, by have := i.isLt; omega⟩

/-- Bool-valued universal quantification over `Fin n → Bool`, by enumeration. -/
def allBool : ∀ (n : Nat), ((Fin n → Bool) → Bool) → Bool
  | 0, f => f Fin.elim0
  | n+1, f =>
      allBool n (fun y => f (consFn false y)) &&
      allBool n (fun y => f (consFn true y))

theorem consFn_eta {n : Nat} (x : Fin (n+1) → Bool) :
    consFn (x 0) (fun i => x ⟨i.val + 1, by omega⟩) = x := by
  funext i
  unfold consFn
  by_cases h : i.val = 0
  · rw [dif_pos h]; congr 1; exact Fin.ext h.symm
  · rw [dif_neg h]; show x _ = x _
    congr 1; apply Fin.ext
    show i.val - 1 + 1 = i.val
    omega

theorem allBool_eq_true : ∀ (n : Nat) (f : (Fin n → Bool) → Bool),
    allBool n f = true ↔ ∀ x, f x = true
  | 0, f => by
    refine ⟨?_, fun h => h _⟩
    intro h x
    have : x = Fin.elim0 := funext (fun i => i.elim0)
    exact this ▸ h
  | n+1, f => by
    simp only [allBool, Bool.and_eq_true]
    rw [allBool_eq_true n, allBool_eq_true n]
    refine ⟨?_, fun h => ⟨fun y => h _, fun y => h _⟩⟩
    rintro ⟨hf, ht⟩ x
    rw [← consFn_eta x]
    cases x 0
    · exact hf _
    · exact ht _

/-- Decidability of universally-quantified Boolean predicates over input
    assignments. Together with `decide`, this lets us check small-`n`
    circuit-complexity claims by enumerating all `2^n` input assignments. -/
instance decForallFinBool {n : Nat} (p : (Fin n → Bool) → Prop) [DecidablePred p] :
    Decidable (∀ x : Fin n → Bool, p x) :=
  decidable_of_iff (allBool n (fun x => decide (p x)) = true) <| by
    rw [allBool_eq_true]
    refine ⟨fun h x => ?_, fun h x => ?_⟩
    · exact of_decide_eq_true (h x)
    · exact decide_eq_true (h x)

/-- A size-0 circuit is just an output wire reference (possibly negated)
    pointing at one of the inputs. So a function has a size-0 circuit iff
    it equals (a possibly negated copy of) some input wire.

    Combined with the `decForallFinBool` instance above, this rewrite
    reduces a goal of the form `¬ HasCircuitOfSize f 0` (for a concrete
    `f` on small `n`) to a fully decidable statement that `decide` closes. -/
theorem hasSize0_iff {n : Nat} {f : (Fin n → Bool) → Bool} :
    HasCircuitOfSize f 0 ↔
      ∃ (idx : Fin n) (neg : Bool),
        ∀ x, f x = (if neg then !x idx else x idx) := by
  constructor
  · rintro ⟨⟨gates, ⟨idx, neg⟩⟩, hc⟩
    match gates with
    | .nil =>
      refine ⟨idx, neg, fun x => ?_⟩
      have := hc x
      simp [Circuit.eval, Ref.eval, GateList.eval] at this
      exact this.symm
  · rintro ⟨idx, neg, h⟩
    refine ⟨⟨.nil, ⟨idx, neg⟩⟩, fun x => ?_⟩
    simp [Circuit.eval, Ref.eval, GateList.eval]
    exact (h x).symm

-- ============================================================
-- Concrete-circuit construction & evaluation helpers
-- ============================================================

/-- Smart constructor for a wire reference at a concrete index.
    The bound proof is auto-discharged by `omega`. -/
abbrev mkRef {b : Nat} (i : Nat) (neg : Bool) (h : i < b := by omega) : Ref b :=
  ⟨⟨i, h⟩, neg⟩

/-- Smart constructor for an AND gate from two concrete index/negation pairs.
    Both bound proofs are auto-discharged by `omega`. -/
abbrev mkGate {b : Nat} (li : Nat) (ln : Bool) (ri : Nat) (rn : Bool)
    (hl : li < b := by omega) (hr : ri < b := by omega) : Gate b :=
  ⟨⟨⟨li, hl⟩, ln⟩, ⟨⟨ri, hr⟩, rn⟩⟩

/-- A literal wire reference inside `gates![...]`: either `i` (positive) or
    `¬i` / `!i` (negated). -/
declare_syntax_cat circLit
syntax num : circLit
syntax "¬" num : circLit
syntax "!" num : circLit

/-- Internal helpers that extract the index / negation bit from a `circLit`. -/
syntax "circLit_idx%" circLit : term
syntax "circLit_neg%" circLit : term

macro_rules
  | `(circLit_idx% $n:num)   => `($n)
  | `(circLit_idx% ¬ $n:num) => `($n)
  | `(circLit_neg% $_:num)   => `(false)
  | `(circLit_neg% ¬ $_:num) => `(true)

/-- A single AND gate written as `lit ∧ lit`. -/
syntax circAnd := circLit " ∧ " circLit

/-- List-style notation for building a `GateList`.
    Each gate is written as `lit ∧ lit`, where each literal is either `i`
    or `¬i` (negated wire). Gates appear in execution (topological) order:
    `gates![g₀, g₁, g₂]` expands to `((.nil.cons g₀).cons g₁).cons g₂`.

    Example: `gates![¬1 ∧ 0, ¬3 ∧ 2]` builds two gates `AND(¬x₁, x₀)` and
    `AND(¬w₃, w₂)` (where `w₃` is the previous gate's output). -/
syntax "gates![" circAnd,* "]" : term
macro_rules
  | `(gates![ $[$as ∧ $bs],* ]) => do
      let mut acc ← `(GateList.nil)
      for (a, b) in as.zip bs do
        acc ← `(GateList.cons $acc
                  (mkGate (circLit_idx% $a) (circLit_neg% $a)
                          (circLit_idx% $b) (circLit_neg% $b)))
      return acc

/-- Tactic for proving `c.eval input = f input` for a concrete circuit `c`
    and a concrete function `f`. Unfolds circuit evaluation, normalizes
    the `Nat.add n k` bounds that arise from the dependent `GateList` index,
    and discharges the remaining Boolean equation with `bv_decide`.

    By default, the head constant of the goal's right-hand side is used as
    the function definition to unfold. Use `circuit_eval Foo.f_idx` to
    override (e.g. when the RHS is not headed by a constant). -/
syntax "circuit_eval" (ppSpace term)? : tactic

elab_rules : tactic
  | `(tactic| circuit_eval $[$override?]?) => do
      Lean.Elab.Tactic.evalTactic
        (← `(tactic| (try unfold Circuit.computes); intros))
      let fStx : Lean.Term ← match override? with
        | some t => pure t
        | none => do
            let goal ← Lean.Elab.Tactic.getMainTarget
            let some (_, _, rhs) := goal.eq?
              | Lean.throwError "circuit_eval: goal is not an equality"
            let some fname := rhs.getAppFn.constName?
              | Lean.throwError "circuit_eval: RHS is not headed by a constant"
            pure ⟨Lean.mkIdent fname⟩
      Lean.Elab.Tactic.evalTactic (← `(tactic| (
          simp only [Circuit.eval, Ref.eval, GateList.eval, Gate.eval, extendEnv,
                     show ∀ a b : Nat, Nat.add a b = a + b from fun _ _ => rfl,
                     $fStx:term]
          bv_decide)))

end Circuits
