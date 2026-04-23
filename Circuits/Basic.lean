/-
  Boolean circuit definitions for empirical circuit complexity.

  A circuit is a DAG of fan-in 2 AND gates, where each wire can be
  optionally negated at zero cost. Circuit size = number of AND gates.
-/
import Std.Tactic.BVDecide
import Lean.Elab.Tactic

namespace Circuits

variable {n bound : Nat}

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
  | cons {kprev : Nat} : GateList n kprev → Gate (n + kprev) → GateList n (kprev + 1)

/-- Build the full wire environment by evaluating gates in order. -/
def GateList.eval (input : Fin n → Bool) {k : Nat} : GateList n k → Fin (n + k) → Bool
  | .nil => input
  | .cons prev gate =>
    let prevEnv := GateList.eval input prev
    extendEnv prevEnv (gate.eval prevEnv)

variable {k : Nat}

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
def GateList.permuteInputs (σ : Fin n → Fin n) {k : Nat} : GateList n k → GateList n k
  | .nil => .nil
  | .cons prev gate => .cons (prev.permuteInputs σ) (gate.permuteInputs n σ (by omega))

/-- Remap a circuit's input wires through a permutation. -/
def Circuit.permuteInputs (c : Circuit n k) (σ : Fin n → Fin n) : Circuit n k :=
  ⟨c.gates.permuteInputs σ, c.output.permuteInputs n σ (by omega)⟩

private theorem ref_eval_permuteInputs_nil {n : Nat} (r : Ref n) (σ : Fin n → Fin n)
    (input : Fin n → Bool) :
    (r.permuteInputs n σ (by omega)).eval input = r.eval (input ∘ σ) := by
  cases r with
  | mk idx neg =>
    simp [Ref.permuteInputs, Ref.eval, Function.comp]

private theorem gate_eval_permuteInputs {n k : Nat} (gate : Gate (n + k))
    (σ : Fin n → Fin n) (envP envO : Fin (n + k) → Bool)
    (henv : ∀ r : Ref (n + k),
      (r.permuteInputs n σ (by omega)).eval envP = r.eval envO) :
    (gate.permuteInputs n σ (by omega)).eval envP = gate.eval envO := by
  cases gate with
  | mk lhs rhs =>
    simp [Gate.permuteInputs, Gate.eval, henv]

private theorem gateList_eval_permuteInputs_ref {n k : Nat} (gates : GateList n k)
    (σ : Fin n → Fin n) (input : Fin n → Bool) :
    ∀ r : Ref (n + k),
      (r.permuteInputs n σ (by omega)).eval ((gates.permuteInputs σ).eval input) =
        r.eval (gates.eval (input ∘ σ)) := by
  induction gates with
  | nil =>
    intro r
    simpa using ref_eval_permuteInputs_nil r σ input
  | cons prev gate ih =>
    rename_i kprev
    intro r
    have hgate : (gate.permuteInputs n σ (by omega)).eval
        ((prev.permuteInputs σ).eval input) = gate.eval (prev.eval (input ∘ σ)) :=
      gate_eval_permuteInputs gate σ ((prev.permuteInputs σ).eval input)
        (prev.eval (input ∘ σ)) ih
    cases r with
    | mk idx neg =>
      by_cases hprev : idx.val < n + kprev
      · by_cases hinput : idx.val < n
        · have ih' :=
            ih ({ index := ⟨idx.val, hprev⟩, negated := neg } : Ref (n + kprev))
          have hσprev : ∀ h : idx.val < n, (σ ⟨idx.val, h⟩).val < n + kprev := by
            intro h
            have := (σ ⟨idx.val, h⟩).isLt
            omega
          simp [Ref.permuteInputs, Ref.eval, GateList.eval, GateList.permuteInputs,
            extendEnv, hprev, hinput, hσprev] at ih' ⊢
          simpa using ih'
        · have ih' :=
            ih ({ index := ⟨idx.val, hprev⟩, negated := neg } : Ref (n + kprev))
          simp [Ref.permuteInputs, Ref.eval, GateList.eval, GateList.permuteInputs,
            extendEnv, hprev, hinput] at ih' ⊢
          simpa using ih'
      · have hnidx : ¬idx.val < n := by omega
        simp [Ref.permuteInputs, Ref.eval, GateList.eval, GateList.permuteInputs,
          extendEnv, hprev, hnidx, hgate]

/-- Evaluating a permuted circuit on input x equals evaluating
    the original circuit on x ∘ σ. The permuted gate list produces
    the same gate outputs because each remapped input reference σ(i)
    reads input(σ(i)) from the base environment, which matches what
    the original circuit reads as (input ∘ σ)(i). -/
theorem Circuit.eval_permuteInputs (c : Circuit n k) (σ : Fin n → Fin n)
    (input : Fin n → Bool) :
    (c.permuteInputs σ).eval input = c.eval (input ∘ σ) := by
  cases c with
  | mk gates output =>
    simpa [Circuit.permuteInputs, Circuit.eval] using
      gateList_eval_permuteInputs_ref gates σ input output

/-- Circuit complexity is invariant under permutation of input variables.
    Given mutually inverse permutations σ and τ, if g(x) = f(x ∘ σ) for all x,
    then f and g have the same circuit complexity. -/
theorem CircuitComplexity_perm {n : Nat} {f g : (Fin n → Bool) → Bool} {k : Nat}
    (σ τ : Fin n → Fin n)
    (_hστ : ∀ i, σ (τ i) = i)
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
def Ref.negateInput (r : Ref bound) (i : Fin n) (_hn : n ≤ bound) : Ref bound :=
  if r.index.val = i.val then ⟨r.index, !r.negated⟩ else r

/-- Negate input wire i in a gate. -/
def Gate.negateInput (g : Gate bound) (i : Fin n) (hn : n ≤ bound) : Gate bound :=
  ⟨g.lhs.negateInput i hn, g.rhs.negateInput i hn⟩

/-- Negate input wire i throughout a gate list. -/
def GateList.negateInput (i : Fin n) {k : Nat} : GateList n k → GateList n k
  | .nil => .nil
  | .cons prev gate => .cons (prev.negateInput i) (gate.negateInput i (by omega))

/-- Negate input wire i in a circuit. -/
def Circuit.negateInput (c : Circuit n k) (i : Fin n) : Circuit n k :=
  ⟨c.gates.negateInput i, c.output.negateInput i (by omega)⟩

private theorem ref_eval_negateInput_nil {n : Nat} (r : Ref n) (i : Fin n)
    (input : Fin n → Bool) :
    (r.negateInput i (by omega)).eval input =
      r.eval (fun j => if j = i then !input j else input j) := by
  cases r with
  | mk idx neg =>
    simp [Ref.negateInput, Ref.eval]
    by_cases h : idx.val = i.val
    · have hidx : idx = i := Fin.ext h
      subst hidx
      cases neg <;> simp
    · have hidx : idx ≠ i := by
        intro heq
        exact h (congrArg Fin.val heq)
      simp [h, hidx]

private theorem gate_eval_negateInput {n k : Nat} (gate : Gate (n + k))
    (i : Fin n) (envN envO : Fin (n + k) → Bool)
    (henv : ∀ r : Ref (n + k), (r.negateInput i (by omega)).eval envN = r.eval envO) :
    (gate.negateInput i (by omega)).eval envN = gate.eval envO := by
  cases gate with
  | mk lhs rhs =>
    simp [Gate.negateInput, Gate.eval, henv]

private theorem gateList_eval_negateInput_ref {n k : Nat} (gates : GateList n k)
    (i : Fin n) (input : Fin n → Bool) :
    ∀ r : Ref (n + k),
      (r.negateInput i (by omega)).eval ((gates.negateInput i).eval input) =
        r.eval (gates.eval (fun j => if j = i then !input j else input j)) := by
  induction gates with
  | nil =>
    intro r
    simpa using ref_eval_negateInput_nil r i input
  | cons prev gate ih =>
    rename_i kprev
    intro r
    have hgate : (gate.negateInput i (by omega)).eval ((prev.negateInput i).eval input) =
        gate.eval (prev.eval (fun j => if j = i then !input j else input j)) :=
      gate_eval_negateInput gate i ((prev.negateInput i).eval input)
        (prev.eval (fun j => if j = i then !input j else input j)) ih
    cases r with
    | mk idx neg =>
      by_cases hprev : idx.val < n + kprev
      · by_cases heq : idx.val = i.val
        · have ih' :=
            ih ({ index := ⟨idx.val, hprev⟩, negated := neg } : Ref (n + kprev))
          have hiprev : i.val < n + kprev := by omega
          simp [Ref.negateInput, Ref.eval, GateList.eval, GateList.negateInput,
            extendEnv, heq, hiprev] at ih' ⊢
          simpa using ih'
        · have ih' :=
            ih ({ index := ⟨idx.val, hprev⟩, negated := neg } : Ref (n + kprev))
          simp [Ref.negateInput, Ref.eval, GateList.eval, GateList.negateInput,
            extendEnv, hprev, heq] at ih' ⊢
          simpa using ih'
      · have hidx : ¬idx.val = i.val := by omega
        simp [Ref.negateInput, Ref.eval, GateList.eval, GateList.negateInput,
          extendEnv, hprev, hidx, hgate]

/-- Evaluating a circuit with negated input wire i on input x equals
    evaluating the original circuit on x with bit i flipped.
    Conceptually straightforward (flip one wire's negation bits) but
    the dependent types in GateList make the induction proof tedious. -/
theorem Circuit.eval_negateInput (c : Circuit n k) (i : Fin n)
    (input : Fin n → Bool) :
    (c.negateInput i).eval input =
    c.eval (fun j => if j = i then !input j else input j) := by
  cases c with
  | mk gates output =>
    simpa [Circuit.negateInput, Circuit.eval] using
      gateList_eval_negateInput_ref gates i input output

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
-- Input minors
-- ============================================================

/-- Substitute each input wire by a literal over a smaller input set.
    Gate wires are shifted from the old input prefix to the new input prefix. -/
def Ref.inputMinor {n m k : Nat} (r : Ref (n + k)) (ρ : Fin n → Ref m) : Ref (m + k) :=
  if h : r.index.val < n then
    let rr := ρ ⟨r.index.val, h⟩
    ⟨⟨rr.index.val, by have := rr.index.isLt; omega⟩, Bool.xor r.negated rr.negated⟩
  else
    ⟨⟨m + (r.index.val - n), by have := r.index.isLt; omega⟩, r.negated⟩

/-- Substitute input literals in a gate. -/
def Gate.inputMinor {n m k : Nat} (g : Gate (n + k)) (ρ : Fin n → Ref m) :
    Gate (m + k) :=
  ⟨g.lhs.inputMinor ρ, g.rhs.inputMinor ρ⟩

/-- Substitute input literals throughout a gate list. -/
def GateList.inputMinor {n m : Nat} (ρ : Fin n → Ref m) {k : Nat} : GateList n k → GateList m k
  | .nil => .nil
  | .cons prev gate => .cons (prev.inputMinor ρ) (gate.inputMinor ρ)

/-- Substitute input literals in a circuit without changing the number of gates. -/
def Circuit.inputMinor {m : Nat} (c : Circuit n k) (ρ : Fin n → Ref m) : Circuit m k :=
  ⟨c.gates.inputMinor ρ, c.output.inputMinor ρ⟩

private theorem ref_eval_inputMinor_nil {n m : Nat} (r : Ref n) (ρ : Fin n → Ref m)
    (input : Fin m → Bool) :
    (r.inputMinor (k := 0) ρ).eval input = r.eval (fun i => (ρ i).eval input) := by
  cases r with
  | mk idx neg =>
    have hidx : idx.val < n := idx.isLt
    simp [Ref.inputMinor, Ref.eval, hidx]
    cases neg <;> cases hρ : (ρ idx).negated <;> simp

private theorem gate_eval_inputMinor {n m k : Nat} (gate : Gate (n + k))
    (ρ : Fin n → Ref m) (envM : Fin (m + k) → Bool) (envN : Fin (n + k) → Bool)
    (henv : ∀ r : Ref (n + k), (r.inputMinor ρ).eval envM = r.eval envN) :
    (gate.inputMinor ρ).eval envM = gate.eval envN := by
  cases gate with
  | mk lhs rhs =>
    simp [Gate.inputMinor, Gate.eval, henv]

private theorem gateList_eval_inputMinor_ref {n m k : Nat} (gates : GateList n k)
    (ρ : Fin n → Ref m) (input : Fin m → Bool) :
    ∀ r : Ref (n + k),
      (r.inputMinor ρ).eval ((gates.inputMinor ρ).eval input) =
        r.eval (gates.eval (fun i => (ρ i).eval input)) := by
  induction gates with
  | nil =>
    intro r
    simpa using ref_eval_inputMinor_nil r ρ input
  | cons prev gate ih =>
    rename_i kprev
    intro r
    have hgate : (gate.inputMinor ρ).eval ((prev.inputMinor ρ).eval input) =
        gate.eval (prev.eval (fun i => (ρ i).eval input)) :=
      gate_eval_inputMinor gate ρ ((prev.inputMinor ρ).eval input)
        (prev.eval (fun i => (ρ i).eval input)) ih
    cases r with
    | mk idx neg =>
      by_cases hinput : idx.val < n
      · have hprev : idx.val < n + kprev := by omega
        have ih' :=
          ih ({ index := ⟨idx.val, hprev⟩, negated := neg } : Ref (n + kprev))
        have hρprev : ∀ h : idx.val < n, (ρ ⟨idx.val, h⟩).index.val < m + kprev := by
          intro h
          have := (ρ ⟨idx.val, h⟩).index.isLt
          omega
        have hρeq : ∀ h : idx.val < n, ρ ⟨idx.val, h⟩ = ρ ⟨idx.val, hinput⟩ := by
          intro h
          apply congrArg ρ
          exact Fin.ext rfl
        simp [Ref.inputMinor, Ref.eval, GateList.eval, GateList.inputMinor,
          extendEnv, hinput, hprev, hρprev, hρeq] at ih' ⊢
        change (if neg = (ρ ⟨idx.val, hinput⟩).negated then
            GateList.eval input (GateList.inputMinor ρ prev)
              ⟨(ρ ⟨idx.val, hinput⟩).index.val, hρprev hinput⟩
          else !GateList.eval input (GateList.inputMinor ρ prev)
              ⟨(ρ ⟨idx.val, hinput⟩).index.val, hρprev hinput⟩) =
          (if neg then
            !GateList.eval (fun i => (ρ i).eval input) prev ⟨idx.val, hprev⟩
          else GateList.eval (fun i => (ρ i).eval input) prev ⟨idx.val, hprev⟩)
        simpa [Ref.eval] using ih'
      · by_cases hprev : idx.val < n + kprev
        · have ih' :=
            ih ({ index := ⟨idx.val, hprev⟩, negated := neg } : Ref (n + kprev))
          have hshift : idx.val - n < kprev := by omega
          simp [Ref.inputMinor, Ref.eval, GateList.eval, GateList.inputMinor,
            extendEnv, hinput, hprev, hshift] at ih' ⊢
          simpa using ih'
        · have hshift : ¬idx.val - n < kprev := by omega
          simp [Ref.inputMinor, Ref.eval, GateList.eval, GateList.inputMinor,
            extendEnv, hinput, hprev, hshift, hgate]

/-- Evaluating an input-minor circuit equals evaluating the original circuit
    after applying the literal substitution to the input environment. -/
theorem Circuit.eval_inputMinor {m : Nat} (c : Circuit n k) (ρ : Fin n → Ref m)
    (input : Fin m → Bool) :
    (c.inputMinor ρ).eval input = c.eval (fun i => (ρ i).eval input) := by
  cases c with
  | mk gates output =>
    simpa [Circuit.inputMinor, Circuit.eval] using gateList_eval_inputMinor_ref gates ρ input output

/-- A circuit for a function induces an equal-size circuit for every input minor. -/
theorem HasCircuitOfSize.inputMinor {n m k : Nat} {f : (Fin n → Bool) → Bool}
    (ρ : Fin n → Ref m) :
    HasCircuitOfSize f k →
      HasCircuitOfSize (fun input : Fin m → Bool => f (fun i => (ρ i).eval input)) k := by
  rintro ⟨c, hc⟩
  exact ⟨c.inputMinor ρ, fun input => by rw [Circuit.eval_inputMinor, hc]⟩

/-- To rule out a circuit for `f`, it suffices to find a hard input minor of `f`. -/
theorem noCircuitOfSize_of_inputMinor {n m k : Nat}
    {f : (Fin n → Bool) → Bool} {g : (Fin m → Bool) → Bool}
    (ρ : Fin n → Ref m)
    (hminor : ∀ input, g input = f (fun i => (ρ i).eval input))
    (hlower : ¬HasCircuitOfSize g k) :
    ¬HasCircuitOfSize f k := by
  intro hf
  obtain ⟨c, hc⟩ := HasCircuitOfSize.inputMinor ρ hf
  exact hlower ⟨c, fun input => by rw [hc input]; exact (hminor input).symm⟩

-- ============================================================
-- Last-gate decomposition
-- ============================================================

/-- A `(k+1)`-gate circuit either ignores the last gate, or computes the
    final gate (possibly negated) from two functions already available from
    the `k`-gate prefix. This is a structural way to reduce lower bounds from
    size `k+1` to questions about which prefix outputs can coexist. -/
theorem HasCircuitOfSize.succ_decompose {n k : Nat} {f : (Fin n → Bool) → Bool} :
    HasCircuitOfSize f (k + 1) →
      HasCircuitOfSize f k ∨
        ∃ (g h : (Fin n → Bool) → Bool),
          HasCircuitOfSize g k ∧ HasCircuitOfSize h k ∧
            ((∀ x, f x = (g x && h x)) ∨
             (∀ x, f x = !(g x && h x))) := by
  rintro ⟨⟨gates, out⟩, hc⟩
  match gates with
  | .cons prev gate =>
    obtain ⟨idx, neg⟩ := out
    by_cases hprev : idx.val < n + k
    · left
      refine ⟨⟨prev, ⟨⟨idx.val, hprev⟩, neg⟩⟩, fun x => ?_⟩
      calc
        (⟨prev, ⟨⟨idx.val, hprev⟩, neg⟩⟩ : Circuit n k).eval x =
            (⟨prev.cons gate, ⟨idx, neg⟩⟩ : Circuit n (k + 1)).eval x := by
          cases neg <;>
            simp [Circuit.eval, GateList.eval, Ref.eval, extendEnv, hprev]
        _ = f x := hc x
    · right
      have hlast : idx.val = n + k := by
        have := idx.isLt
        omega
      let g : (Fin n → Bool) → Bool := fun x => gate.lhs.eval (prev.eval x)
      let h : (Fin n → Bool) → Bool := fun x => gate.rhs.eval (prev.eval x)
      refine ⟨g, h, ?_, ?_, ?_⟩
      · exact ⟨⟨prev, gate.lhs⟩, fun _ => rfl⟩
      · exact ⟨⟨prev, gate.rhs⟩, fun _ => rfl⟩
      · cases neg
        · left
          intro x
          calc
            f x = (⟨prev.cons gate, ⟨idx, false⟩⟩ : Circuit n (k + 1)).eval x :=
              (hc x).symm
            _ = (g x && h x) := by
              simp [Circuit.eval, GateList.eval, Gate.eval, Ref.eval, extendEnv, hlast, g, h]
        · right
          intro x
          calc
            f x = (⟨prev.cons gate, ⟨idx, true⟩⟩ : Circuit n (k + 1)).eval x :=
              (hc x).symm
            _ = !(g x && h x) := by
              cases hgl : gate.lhs.eval (prev.eval x) <;>
                cases hgr : gate.rhs.eval (prev.eval x) <;>
                simp [Circuit.eval, GateList.eval, Gate.eval, Ref.eval, extendEnv, hlast,
                  g, h]

/-- Contrapositive form of `HasCircuitOfSize.succ_decompose`, convenient for
    lower bounds. To rule out size `k+1`, rule out size `k` and every possible
    final AND/NAND decomposition over two `k`-gate-computable prefix outputs. -/
theorem noCircuitOfSize_succ_of_no_decompose {n k : Nat}
    {f : (Fin n → Bool) → Bool}
    (hsmall : ¬HasCircuitOfSize f k)
    (hdecomp : ∀ (g h : (Fin n → Bool) → Bool),
      HasCircuitOfSize g k → HasCircuitOfSize h k →
        ¬((∀ x, f x = (g x && h x)) ∨
          (∀ x, f x = !(g x && h x)))) :
    ¬HasCircuitOfSize f (k + 1) := by
  intro hf
  rcases HasCircuitOfSize.succ_decompose hf with hfsmall | hlast
  · exact hsmall hfsmall
  · rcases hlast with ⟨g, h, hg, hh, hcomb⟩
    exact hdecomp g h hg hh hcomb

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

/-- A size-1 circuit is one AND gate over two input literals, followed by
    an output reference to either an input wire or that gate output. -/
theorem hasSize1_iff {n : Nat} {f : (Fin n → Bool) → Bool} :
    HasCircuitOfSize f 1 ↔
      ∃ (li : Fin n) (ln : Bool) (ri : Fin n) (rn : Bool)
        (oi : Fin (n + 1)) (on : Bool),
        ∀ x, f x =
          (⟨oi, on⟩ : Ref (n + 1)).eval
            (extendEnv x ((⟨⟨li, ln⟩, ⟨ri, rn⟩⟩ : Gate n).eval x)) := by
  constructor
  · rintro ⟨⟨gates, out⟩, hc⟩
    match gates with
    | .cons .nil gate =>
      obtain ⟨⟨li, ln⟩, ⟨ri, rn⟩⟩ := gate
      obtain ⟨oi, on⟩ := out
      refine ⟨li, ln, ri, rn, oi, on, fun x => ?_⟩
      exact (hc x).symm
  · rintro ⟨li, ln, ri, rn, oi, on, h⟩
    refine ⟨⟨.cons .nil (⟨⟨li, ln⟩, ⟨ri, rn⟩⟩ : Gate n), ⟨oi, on⟩⟩, fun x => ?_⟩
    exact (h x).symm

/-- A size-2 circuit is two AND gates in topological order, followed by
    an output reference to either an input wire or one of the two gates. -/
theorem hasSize2_iff {n : Nat} {f : (Fin n → Bool) → Bool} :
    HasCircuitOfSize f 2 ↔
      ∃ (g0li : Fin n) (g0ln : Bool) (g0ri : Fin n) (g0rn : Bool)
        (g1li : Fin (n + 1)) (g1ln : Bool) (g1ri : Fin (n + 1)) (g1rn : Bool)
        (oi : Fin (n + 2)) (on : Bool),
        ∀ x, f x =
          (⟨oi, on⟩ : Ref (n + 2)).eval
            (extendEnv
              (extendEnv x
                ((⟨⟨g0li, g0ln⟩, ⟨g0ri, g0rn⟩⟩ : Gate n).eval x))
              ((⟨⟨g1li, g1ln⟩, ⟨g1ri, g1rn⟩⟩ : Gate (n + 1)).eval
                (extendEnv x
                  ((⟨⟨g0li, g0ln⟩, ⟨g0ri, g0rn⟩⟩ : Gate n).eval x)))) := by
  constructor
  · rintro ⟨⟨gates, out⟩, hc⟩
    match gates with
    | .cons (.cons .nil gate0) gate1 =>
      obtain ⟨⟨g0li, g0ln⟩, ⟨g0ri, g0rn⟩⟩ := gate0
      obtain ⟨⟨g1li, g1ln⟩, ⟨g1ri, g1rn⟩⟩ := gate1
      obtain ⟨oi, on⟩ := out
      refine ⟨g0li, g0ln, g0ri, g0rn, g1li, g1ln, g1ri, g1rn, oi, on, fun x => ?_⟩
      exact (hc x).symm
  · rintro ⟨g0li, g0ln, g0ri, g0rn, g1li, g1ln, g1ri, g1rn, oi, on, h⟩
    let gate0 : Gate n := ⟨⟨g0li, g0ln⟩, ⟨g0ri, g0rn⟩⟩
    let gate1 : Gate (n + 1) := ⟨⟨g1li, g1ln⟩, ⟨g1ri, g1rn⟩⟩
    refine ⟨⟨.cons (.cons .nil gate0) gate1, ⟨oi, on⟩⟩, fun x => ?_⟩
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
