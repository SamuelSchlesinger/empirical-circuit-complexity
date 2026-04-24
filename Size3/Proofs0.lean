import Std.Tactic.BVDecide
import Circuits.Basic
import Size2.Proofs0
import Size3.Defs0

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
set_option profiler true
set_option profiler.threshold 200

namespace Size3.Proofs0

open Circuits

private def f_27_xorMinor : Fin 3 → Ref 2 := fun i =>
  if i.val = 0 then mkRef 0 false
  else if i.val = 1 then mkRef 1 true
  else mkRef 1 false

private def f_60_xorMinor : Fin 3 → Ref 2 := fun i =>
  if i.val = 0 then mkRef 0 false
  else if i.val = 1 then mkRef 0 false
  else mkRef 1 false

private def inputMask (i : Fin 3) : BitVec 8 :=
  if i.val = 0 then 0xaa#8 else if i.val = 1 then 0xcc#8 else 0xf0#8

private def inputOfBit (bit : Nat) : Fin 3 → Bool :=
  fun i => (inputMask i).getLsbD bit

private def extendEnvMask {n : Nat} (env : Fin n → BitVec 8) (val : BitVec 8) :
    Fin (n + 1) → BitVec 8 :=
  fun i => if h : i.val < n then env ⟨i.val, h⟩ else val

private def refEvalMask {bound : Nat} (r : Ref bound)
    (env : Fin bound → BitVec 8) : BitVec 8 :=
  if r.negated then ~~~(env r.index) else env r.index

private def gateEvalMask {bound : Nat} (g : Gate bound)
    (env : Fin bound → BitVec 8) : BitVec 8 :=
  refEvalMask g.lhs env &&& refEvalMask g.rhs env

private theorem refEvalMask_get {bound : Nat} (r : Ref bound)
    (envBV : Fin bound → BitVec 8) (envBool : Fin bound → Bool) (bit : Nat)
    (hbit : bit < 8)
    (henv : ∀ i, (envBV i).getLsbD bit = envBool i) :
    (refEvalMask r envBV).getLsbD bit = r.eval envBool := by
  cases r with
  | mk idx neg =>
    cases neg
    · simpa [refEvalMask, Ref.eval] using henv idx
    · simp [refEvalMask, Ref.eval, hbit]
      exact henv idx

private theorem gateEvalMask_get {bound : Nat} (g : Gate bound)
    (envBV : Fin bound → BitVec 8) (envBool : Fin bound → Bool) (bit : Nat)
    (hbit : bit < 8)
    (henv : ∀ i, (envBV i).getLsbD bit = envBool i) :
    (gateEvalMask g envBV).getLsbD bit = g.eval envBool := by
  cases g with
  | mk lhs rhs =>
    simp [gateEvalMask, Gate.eval, hbit]
    change ((refEvalMask lhs envBV).getLsbD bit &&
      (refEvalMask rhs envBV).getLsbD bit) = (lhs.eval envBool && rhs.eval envBool)
    rw [refEvalMask_get lhs envBV envBool bit hbit henv,
      refEvalMask_get rhs envBV envBool bit hbit henv]

private theorem extendEnvMask_get {n : Nat} (envBV : Fin n → BitVec 8)
    (envBool : Fin n → Bool) (valBV : BitVec 8) (valBool : Bool)
    (bit : Nat)
    (henv : ∀ i, (envBV i).getLsbD bit = envBool i)
    (hval : valBV.getLsbD bit = valBool) :
    ∀ i, (extendEnvMask envBV valBV i).getLsbD bit =
      extendEnv envBool valBool i := by
  intro i
  by_cases h : i.val < n
  · simp [extendEnvMask, extendEnv, h, henv]
  · simp [extendEnvMask, extendEnv, h, hval]

private def size3MaskFin (g0 : Gate 3) (g1 : Gate 4) (g2 : Gate 5)
    (out : Ref 6) : BitVec 8 :=
  let v0 := gateEvalMask g0 inputMask
  let env1 := extendEnvMask inputMask v0
  let v1 := gateEvalMask g1 env1
  let env2 := extendEnvMask env1 v1
  let v2 := gateEvalMask g2 env2
  let env3 := extendEnvMask env2 v2
  refEvalMask out env3

private theorem size3MaskFin_get (g0 : Gate 3) (g1 : Gate 4) (g2 : Gate 5)
    (out : Ref 6) (bit : Nat) (hbit : bit < 8) :
    (size3MaskFin g0 g1 g2 out).getLsbD bit =
      (⟨.cons (.cons (.cons .nil g0) g1) g2, out⟩ : Circuit 3 3).eval
        (inputOfBit bit) := by
  let env0BV := inputMask
  let env0Bool := inputOfBit bit
  let v0BV := gateEvalMask g0 env0BV
  let v0Bool := g0.eval env0Bool
  let env1BV := extendEnvMask env0BV v0BV
  let env1Bool := extendEnv env0Bool v0Bool
  let v1BV := gateEvalMask g1 env1BV
  let v1Bool := g1.eval env1Bool
  let env2BV := extendEnvMask env1BV v1BV
  let env2Bool := extendEnv env1Bool v1Bool
  let v2BV := gateEvalMask g2 env2BV
  let v2Bool := g2.eval env2Bool
  let env3BV := extendEnvMask env2BV v2BV
  let env3Bool := extendEnv env2Bool v2Bool
  have henv0 : ∀ i, (env0BV i).getLsbD bit = env0Bool i := by
    intro i
    rfl
  have hv0 : v0BV.getLsbD bit = v0Bool :=
    gateEvalMask_get g0 env0BV env0Bool bit hbit henv0
  have henv1 : ∀ i, (env1BV i).getLsbD bit = env1Bool i :=
    extendEnvMask_get env0BV env0Bool v0BV v0Bool bit henv0 hv0
  have hv1 : v1BV.getLsbD bit = v1Bool :=
    gateEvalMask_get g1 env1BV env1Bool bit hbit henv1
  have henv2 : ∀ i, (env2BV i).getLsbD bit = env2Bool i :=
    extendEnvMask_get env1BV env1Bool v1BV v1Bool bit henv1 hv1
  have hv2 : v2BV.getLsbD bit = v2Bool :=
    gateEvalMask_get g2 env2BV env2Bool bit hbit henv2
  have henv3 : ∀ i, (env3BV i).getLsbD bit = env3Bool i :=
    extendEnvMask_get env2BV env2Bool v2BV v2Bool bit henv2 hv2
  change (refEvalMask out env3BV).getLsbD bit = out.eval env3Bool
  exact refEvalMask_get out env3BV env3Bool bit hbit henv3

private def bitNot (x : BitVec 8) : BitVec 8 := ~~~x

private def containsMask (target : BitVec 8) : List (BitVec 8) → Bool
  | [] => false
  | x :: xs => if x = target then true else containsMask target xs

private def insertMask (x : BitVec 8) : List (BitVec 8) → List (BitVec 8)
  | [] => [x]
  | y :: ys =>
      if x.toNat < y.toNat then x :: y :: ys
      else if x = y then y :: ys
      else y :: insertMask x ys

private def insertGateMasks (g : BitVec 8) (state : List (BitVec 8)) : List (BitVec 8) :=
  insertMask (bitNot g) (insertMask g state)

private def initState : List (BitVec 8) :=
  [0x0f#8, 0x33#8, 0x55#8, 0xaa#8, 0xcc#8, 0xf0#8]

private def stateEq : List (BitVec 8) → List (BitVec 8) → Bool
  | [], [] => true
  | x :: xs, y :: ys => if x = y then stateEq xs ys else false
  | _, _ => false

private def containsState (s : List (BitVec 8)) : List (List (BitVec 8)) → Bool
  | [] => false
  | t :: ts => stateEq s t || containsState s ts

private def insertState (s : List (BitVec 8)) (ss : List (List (BitVec 8))) :
    List (List (BitVec 8)) :=
  if containsState s ss then ss else s :: ss

private def nextFromState (state : List (BitVec 8)) : List (List (BitVec 8)) :=
  state.foldl (fun acc a =>
    state.foldl (fun acc b =>
      insertState (insertGateMasks (a &&& b) state) acc) acc) []

private def appendStates (xs ys : List (List (BitVec 8))) : List (List (BitVec 8)) :=
  xs.foldl (fun acc s => insertState s acc) ys

private def nextFrontier (states : List (List (BitVec 8))) : List (List (BitVec 8)) :=
  states.foldl (fun acc s => appendStates (nextFromState s) acc) []

private def frontier : Nat → List (List (BitVec 8))
  | 0 => [initState]
  | n + 1 => nextFrontier (frontier n)

private def finalCanOutput (target : BitVec 8) (state : List (BitVec 8)) : Bool :=
  containsMask target state ||
    state.any (fun a => state.any (fun b =>
      let g := a &&& b
      if g = target then true else bitNot g = target))

private def frontierCanOutput (fuel : Nat) (target : BitVec 8) : Bool :=
  (frontier fuel).any (finalCanOutput target)

private theorem stateEq_self : ∀ s : List (BitVec 8), stateEq s s = true
  | [] => rfl
  | _ :: xs => by simp [stateEq, stateEq_self xs]

private theorem stateEq_eq : ∀ {s t : List (BitVec 8)}, stateEq s t = true → s = t
  | [], [], _ => rfl
  | _ :: _, [], h => by simp [stateEq] at h
  | [], _ :: _, h => by simp [stateEq] at h
  | x :: xs, y :: ys, h => by
      by_cases hxy : x = y
      · subst hxy
        simp [stateEq] at h
        exact congrArg (List.cons x) (stateEq_eq h)
      · simp [stateEq, hxy] at h

private theorem containsState_insert_self (s : List (BitVec 8)) (ss : List (List (BitVec 8))) :
    containsState s (insertState s ss) = true := by
  unfold insertState
  by_cases h : containsState s ss = true
  · simp [h]
  · simp [h, containsState, stateEq_self]

private theorem containsState_insert_of_stateEq {s t : List (BitVec 8)}
    (h : stateEq s t = true) (ss : List (List (BitVec 8))) :
    containsState s (insertState t ss) = true := by
  have hst : s = t := stateEq_eq h
  simpa [hst] using containsState_insert_self t ss

private theorem containsState_insert_of_contains {s t : List (BitVec 8)}
    {ss : List (List (BitVec 8))}
    (h : containsState s ss = true) :
    containsState s (insertState t ss) = true := by
  unfold insertState
  by_cases ht : containsState t ss = true
  · simp [ht, h]
  · simp [ht, containsState, h]

private theorem any_of_containsMask {p : BitVec 8 → Bool} {x : BitVec 8} :
    ∀ {xs : List (BitVec 8)}, containsMask x xs = true → p x = true → xs.any p = true
  | [], hmem, _ => by simp [containsMask] at hmem
  | y :: ys, hmem, hp => by
      by_cases hxy : y = x
      · subst hxy
        simp [hp]
      · simp [containsMask, hxy] at hmem
        simp [List.any, any_of_containsMask hmem hp]

private theorem any_of_containsState {p : List (BitVec 8) → Bool} {x : List (BitVec 8)} :
    ∀ {xs : List (List (BitVec 8))}, containsState x xs = true → p x = true →
      xs.any p = true
  | [], hmem, _ => by simp [containsState] at hmem
  | y :: ys, hmem, hp => by
      by_cases hxy : stateEq x y = true
      · have h : x = y := stateEq_eq hxy
        subst h
        simp [hp]
      · simp [containsState, hxy] at hmem
        simp [List.any, any_of_containsState hmem hp]

private theorem fold_insertState_preserve (target : List (BitVec 8))
    (f : BitVec 8 → List (BitVec 8)) :
    ∀ (xs : List (BitVec 8)) (acc : List (List (BitVec 8))),
      containsState target acc = true →
      containsState target (xs.foldl (fun acc x => insertState (f x) acc) acc) = true
  | [], _, h => h
  | x :: xs, acc, h =>
      fold_insertState_preserve target f xs (insertState (f x) acc)
        (containsState_insert_of_contains h)

private theorem fold_insertState_hit (target : List (BitVec 8))
    (f : BitVec 8 → List (BitVec 8)) :
    ∀ {xs : List (BitVec 8)} {acc : List (List (BitVec 8))} {x : BitVec 8},
      containsMask x xs = true → target = f x →
      containsState target (xs.foldl (fun acc y => insertState (f y) acc) acc) = true
  | [], _, _, hmem, _ => by simp [containsMask] at hmem
  | y :: ys, acc, x, hmem, htarget => by
      by_cases hyx : y = x
      · subst hyx
        have hself : containsState target (insertState (f y) acc) = true := by
          rw [htarget]
          exact containsState_insert_self (f y) acc
        exact fold_insertState_preserve target f ys (insertState (f y) acc) hself
      · simp [containsMask, hyx] at hmem
        exact fold_insertState_hit target f (xs := ys) (acc := insertState (f y) acc)
          (x := x) hmem htarget

private theorem contains_init_ref (r : Ref 3) :
    containsMask (refEvalMask r inputMask) initState = true := by
  cases r with
  | mk idx neg =>
    cases idx with
    | mk i hi =>
      have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by omega
      rcases hi' with rfl | rfl | rfl <;>
        cases neg <;> simp [containsMask, refEvalMask, inputMask, initState]

private theorem inner_preserve (state target : List (BitVec 8)) (a : BitVec 8) :
    ∀ acc, containsState target acc = true →
      containsState target
        (state.foldl (fun acc b => insertState (insertGateMasks (a &&& b) state) acc) acc) =
        true := by
  intro acc h
  exact fold_insertState_preserve target (fun b => insertGateMasks (a &&& b) state)
    state acc h

private theorem inner_hit {state : List (BitVec 8)} {a b : BitVec 8}
    (hb : containsMask b state = true) :
    ∀ acc,
      containsState (insertGateMasks (a &&& b) state)
        (state.foldl (fun acc b' => insertState (insertGateMasks (a &&& b') state) acc)
          acc) = true := by
  intro acc
  exact fold_insertState_hit (insertGateMasks (a &&& b) state)
    (fun b' => insertGateMasks (a &&& b') state) hb rfl

private theorem fold_step_preserve (target : List (BitVec 8))
    (step : BitVec 8 → List (List (BitVec 8)) → List (List (BitVec 8)))
    (hstep : ∀ x acc, containsState target acc = true →
      containsState target (step x acc) = true) :
    ∀ (xs : List (BitVec 8)) (acc : List (List (BitVec 8))),
      containsState target acc = true →
      containsState target (xs.foldl (fun acc x => step x acc) acc) = true
  | [], _, h => h
  | x :: xs, acc, h =>
      fold_step_preserve target step hstep xs (step x acc) (hstep x acc h)

private theorem fold_step_hit (target : List (BitVec 8))
    (step : BitVec 8 → List (List (BitVec 8)) → List (List (BitVec 8)))
    (hstep : ∀ x acc, containsState target acc = true →
      containsState target (step x acc) = true) :
    ∀ {xs : List (BitVec 8)} {acc : List (List (BitVec 8))} {x : BitVec 8},
      containsMask x xs = true →
      (∀ acc, containsState target (step x acc) = true) →
      containsState target (xs.foldl (fun acc y => step y acc) acc) = true
  | [], _, _, hmem, _ => by simp [containsMask] at hmem
  | y :: ys, acc, x, hmem, hhit => by
      by_cases hyx : y = x
      · subst hyx
        exact fold_step_preserve target step hstep ys (step y acc) (hhit acc)
      · simp [containsMask, hyx] at hmem
        exact fold_step_hit target step hstep (xs := ys) (acc := step y acc) (x := x)
          hmem hhit

private theorem nextFromState_contains {state : List (BitVec 8)} {a b : BitVec 8}
    (ha : containsMask a state = true) (hb : containsMask b state = true) :
    containsState (insertGateMasks (a &&& b) state) (nextFromState state) = true := by
  unfold nextFromState
  exact fold_step_hit (insertGateMasks (a &&& b) state)
    (fun a' acc =>
      state.foldl (fun acc b' => insertState (insertGateMasks (a' &&& b') state) acc) acc)
    (fun a' acc h => inner_preserve state (insertGateMasks (a &&& b) state) a' acc h)
    ha
    (fun acc => inner_hit hb acc)

private theorem appendStates_preserve (target : List (BitVec 8)) :
    ∀ xs acc, containsState target acc = true →
      containsState target (appendStates xs acc) = true := by
  intro xs acc h
  unfold appendStates
  induction xs generalizing acc with
  | nil => exact h
  | cons x xs ih =>
      exact ih (insertState x acc) (containsState_insert_of_contains h)

private theorem appendStates_hit {target : List (BitVec 8)} :
    ∀ {xs acc}, containsState target xs = true →
      containsState target (appendStates xs acc) = true
  | [], _, h => by simp [containsState] at h
  | x :: xs, acc, h => by
      unfold appendStates
      by_cases hx : stateEq target x = true
      · exact appendStates_preserve target xs (insertState x acc)
          (containsState_insert_of_stateEq hx acc)
      · simp [containsState, hx] at h
        exact appendStates_hit (xs := xs) (acc := insertState x acc) h

private theorem fold_state_step_preserve (target : List (BitVec 8))
    (step : List (BitVec 8) → List (List (BitVec 8)) → List (List (BitVec 8)))
    (hstep : ∀ x acc, containsState target acc = true →
      containsState target (step x acc) = true) :
    ∀ (xs : List (List (BitVec 8))) (acc : List (List (BitVec 8))),
      containsState target acc = true →
      containsState target (xs.foldl (fun acc x => step x acc) acc) = true
  | [], _, h => h
  | x :: xs, acc, h =>
      fold_state_step_preserve target step hstep xs (step x acc) (hstep x acc h)

private theorem fold_state_step_hit (target selected : List (BitVec 8))
    (step : List (BitVec 8) → List (List (BitVec 8)) → List (List (BitVec 8)))
    (hstep : ∀ x acc, containsState target acc = true →
      containsState target (step x acc) = true)
    (hhit : ∀ acc, containsState target (step selected acc) = true) :
    ∀ {xs acc}, containsState selected xs = true →
      containsState target (xs.foldl (fun acc y => step y acc) acc) = true
  | [], _, hmem => by simp [containsState] at hmem
  | y :: ys, acc, hmem => by
      by_cases hy : stateEq selected y = true
      · have hsel : selected = y := stateEq_eq hy
        have hpres := fold_state_step_preserve target step hstep ys (step selected acc) (hhit acc)
        simpa [hsel] using hpres
      · simp [containsState, hy] at hmem
        exact fold_state_step_hit target selected step hstep hhit
          (xs := ys) (acc := step y acc) hmem

private theorem nextFrontier_contains {states : List (List (BitVec 8))}
    {state target : List (BitVec 8)}
    (hstate : containsState state states = true)
    (hnext : containsState target (nextFromState state) = true) :
    containsState target (nextFrontier states) = true := by
  unfold nextFrontier
  exact fold_state_step_hit target state
    (fun s acc => appendStates (nextFromState s) acc)
    (fun _ acc h => appendStates_preserve target _ acc h)
    (fun acc => appendStates_hit (xs := nextFromState state) (acc := acc) hnext)
    hstate

private def state1 (m0 : BitVec 8) : List (BitVec 8) :=
  insertGateMasks m0 initState

private def state2 (m0 m1 : BitVec 8) : List (BitVec 8) :=
  insertGateMasks m1 (state1 m0)

private theorem contains_insert_self (x : BitVec 8) (xs : List (BitVec 8)) :
    containsMask x (insertMask x xs) = true := by
  unfold insertMask
  match xs with
  | [] => simp [containsMask]
  | y :: ys =>
      by_cases hlt : x.toNat < y.toNat
      · simp [hlt, containsMask]
      · by_cases hxy : x = y
        · simp [hxy, containsMask]
        · simp [hlt, hxy, containsMask, contains_insert_self x ys]

private theorem contains_insert_of_contains {x y : BitVec 8} {xs : List (BitVec 8)}
    (h : containsMask x xs = true) :
    containsMask x (insertMask y xs) = true := by
  induction xs with
  | nil => simp [containsMask] at h
  | cons z zs ih =>
      unfold insertMask
      by_cases hyz_lt : y.toNat < z.toNat
      · simp [hyz_lt, containsMask]
        by_cases hzx : z = x
        · exact Or.inr (Or.inl hzx)
        · simp [containsMask, hzx] at h
          exact Or.inr (Or.inr h)
      · by_cases hyz : y = z
        · simp [hyz, h]
        · simp [hyz_lt, hyz, containsMask]
          by_cases hzx : z = x
          · exact Or.inl hzx
          · simp [containsMask, hzx] at h
            exact Or.inr (ih h)

private theorem contains_state1_old {x m0 : BitVec 8}
    (h : containsMask x initState = true) : containsMask x (state1 m0) = true := by
  unfold state1 insertGateMasks
  exact contains_insert_of_contains (contains_insert_of_contains h)

private theorem contains_state1_m0 (m0 : BitVec 8) : containsMask m0 (state1 m0) = true := by
  unfold state1 insertGateMasks
  exact contains_insert_of_contains (contains_insert_self m0 initState)

private theorem contains_state1_not_m0 (m0 : BitVec 8) :
    containsMask (bitNot m0) (state1 m0) = true := by
  unfold state1 insertGateMasks
  exact contains_insert_self (bitNot m0) (insertMask m0 initState)

private theorem contains_ref4 (r : Ref 4) (g0 : BitVec 8) :
    containsMask (refEvalMask r (extendEnvMask inputMask g0)) (state1 g0) = true := by
  cases r with
  | mk idx neg =>
    cases idx with
    | mk i hi =>
      have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases hi' with rfl | rfl | rfl | rfl
      all_goals cases neg
      all_goals simp [refEvalMask, extendEnvMask]
      · exact contains_state1_old (contains_init_ref (mkRef 0 false : Ref 3))
      · exact contains_state1_old (contains_init_ref (mkRef 0 true : Ref 3))
      · exact contains_state1_old (contains_init_ref (mkRef 1 false : Ref 3))
      · exact contains_state1_old (contains_init_ref (mkRef 1 true : Ref 3))
      · exact contains_state1_old (contains_init_ref (mkRef 2 false : Ref 3))
      · exact contains_state1_old (contains_init_ref (mkRef 2 true : Ref 3))
      · exact contains_state1_m0 g0
      · exact contains_state1_not_m0 g0

private theorem contains_state2_state1 {x m0 m1 : BitVec 8}
    (h : containsMask x (state1 m0) = true) : containsMask x (state2 m0 m1) = true := by
  unfold state2 insertGateMasks
  exact contains_insert_of_contains (contains_insert_of_contains h)

private theorem contains_state2_m1 (m0 m1 : BitVec 8) :
    containsMask m1 (state2 m0 m1) = true := by
  unfold state2 insertGateMasks
  exact contains_insert_of_contains (contains_insert_self m1 (state1 m0))

private theorem contains_state2_not_m1 (m0 m1 : BitVec 8) :
    containsMask (bitNot m1) (state2 m0 m1) = true := by
  unfold state2 insertGateMasks
  exact contains_insert_self (bitNot m1) (insertMask m1 (state1 m0))

private theorem contains_ref5 (r : Ref 5) (g0 g1 : BitVec 8) :
    containsMask (refEvalMask r (extendEnvMask (extendEnvMask inputMask g0) g1))
      (state2 g0 g1) = true := by
  cases r with
  | mk idx neg =>
    cases idx with
    | mk i hi =>
      have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
      rcases hi' with rfl | rfl | rfl | rfl | rfl
      all_goals cases neg
      all_goals simp [refEvalMask, extendEnvMask]
      · exact contains_state2_state1 (contains_ref4 (mkRef 0 false : Ref 4) g0)
      · exact contains_state2_state1 (contains_ref4 (mkRef 0 true : Ref 4) g0)
      · exact contains_state2_state1 (contains_ref4 (mkRef 1 false : Ref 4) g0)
      · exact contains_state2_state1 (contains_ref4 (mkRef 1 true : Ref 4) g0)
      · exact contains_state2_state1 (contains_ref4 (mkRef 2 false : Ref 4) g0)
      · exact contains_state2_state1 (contains_ref4 (mkRef 2 true : Ref 4) g0)
      · exact contains_state2_state1 (contains_ref4 (mkRef 3 false : Ref 4) g0)
      · exact contains_state2_state1 (contains_ref4 (mkRef 3 true : Ref 4) g0)
      · exact contains_state2_m1 g0 g1
      · exact contains_state2_not_m1 g0 g1

private theorem state2_in_frontier (g0 : Gate 3) (g1 : Gate 4) :
    let m0 := gateEvalMask g0 inputMask
    let env1 := extendEnvMask inputMask m0
    let m1 := gateEvalMask g1 env1
    containsState (state2 m0 m1) (frontier 2) = true := by
  intro m0 env1 m1
  have hs0 : containsState initState (frontier 0) = true := by
    simp [frontier, containsState, stateEq_self]
  have hnext0 : containsState (state1 m0) (nextFromState initState) = true := by
    apply nextFromState_contains
    · exact contains_init_ref g0.lhs
    · exact contains_init_ref g0.rhs
  have hs1 : containsState (state1 m0) (frontier 1) = true := by
    change containsState (state1 m0) (nextFrontier (frontier 0)) = true
    exact nextFrontier_contains hs0 hnext0
  have hnext1 : containsState (state2 m0 m1) (nextFromState (state1 m0)) = true := by
    apply nextFromState_contains
    · exact contains_ref4 g1.lhs m0
    · exact contains_ref4 g1.rhs m0
  change containsState (state2 m0 m1) (nextFrontier (frontier 1)) = true
  exact nextFrontier_contains hs1 hnext1

private theorem finalCanOutput_of_contains {target : BitVec 8} {state : List (BitVec 8)}
    (h : containsMask target state = true) :
    finalCanOutput target state = true := by
  simp [finalCanOutput, h]

private theorem finalCanOutput_of_and {a b : BitVec 8} {state : List (BitVec 8)}
    (ha : containsMask a state = true) (hb : containsMask b state = true) :
    finalCanOutput (a &&& b) state = true := by
  have hinner :
      state.any (fun b' =>
        let g := a &&& b'
        if g = a &&& b then true else bitNot g = a &&& b) = true := by
    exact any_of_containsMask hb (by simp)
  have houter :
      state.any (fun a' =>
        state.any (fun b' =>
          let g := a' &&& b'
          if g = a &&& b then true else bitNot g = a &&& b)) = true := by
    exact any_of_containsMask ha hinner
  unfold finalCanOutput
  rw [houter]
  simp

private theorem finalCanOutput_of_nand {a b : BitVec 8} {state : List (BitVec 8)}
    (ha : containsMask a state = true) (hb : containsMask b state = true) :
    finalCanOutput (bitNot (a &&& b)) state = true := by
  have hinner :
      state.any (fun b' =>
        let g := a &&& b'
        if g = bitNot (a &&& b) then true else bitNot g = bitNot (a &&& b)) = true := by
    exact any_of_containsMask hb (by simp [bitNot])
  have houter :
      state.any (fun a' =>
        state.any (fun b' =>
          let g := a' &&& b'
          if g = bitNot (a &&& b) then true else bitNot g = bitNot (a &&& b))) = true := by
    exact any_of_containsMask ha hinner
  unfold finalCanOutput
  rw [houter]
  simp

private theorem finalCanOutput_size3 (g0 : Gate 3) (g1 : Gate 4) (g2 : Gate 5)
    (out : Ref 6) :
    let m0 := gateEvalMask g0 inputMask
    let env1 := extendEnvMask inputMask m0
    let m1 := gateEvalMask g1 env1
    let env2 := extendEnvMask env1 m1
    let m2 := gateEvalMask g2 env2
    let env3 := extendEnvMask env2 m2
    finalCanOutput (refEvalMask out env3) (state2 m0 m1) = true := by
  intro m0 env1 m1 env2 m2 env3
  cases out with
  | mk idx neg =>
    cases idx with
    | mk i hi =>
      have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
      rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals cases neg
      all_goals simp [refEvalMask]
      · exact finalCanOutput_of_contains (contains_ref5 (mkRef 0 false : Ref 5) m0 m1)
      · exact finalCanOutput_of_contains (contains_ref5 (mkRef 0 true : Ref 5) m0 m1)
      · exact finalCanOutput_of_contains (contains_ref5 (mkRef 1 false : Ref 5) m0 m1)
      · exact finalCanOutput_of_contains (contains_ref5 (mkRef 1 true : Ref 5) m0 m1)
      · exact finalCanOutput_of_contains (contains_ref5 (mkRef 2 false : Ref 5) m0 m1)
      · exact finalCanOutput_of_contains (contains_ref5 (mkRef 2 true : Ref 5) m0 m1)
      · exact finalCanOutput_of_contains (contains_ref5 (mkRef 3 false : Ref 5) m0 m1)
      · exact finalCanOutput_of_contains (contains_ref5 (mkRef 3 true : Ref 5) m0 m1)
      · exact finalCanOutput_of_contains (contains_ref5 (mkRef 4 false : Ref 5) m0 m1)
      · exact finalCanOutput_of_contains (contains_ref5 (mkRef 4 true : Ref 5) m0 m1)
      · exact finalCanOutput_of_and (contains_ref5 g2.lhs m0 m1) (contains_ref5 g2.rhs m0 m1)
      · exact finalCanOutput_of_nand (contains_ref5 g2.lhs m0 m1) (contains_ref5 g2.rhs m0 m1)

private theorem f30_frontier_false : frontierCanOutput 2 0x1e#8 = false := by
  rfl

/-- Generic size-3 lower bound via the frontier search.  If
    `frontierCanOutput 2 mask = false` (i.e., no 3-gate circuit can produce the
    bitvector `mask` over the canonical 8 inputs) and `f` agrees with `mask`
    bit-by-bit on the canonical inputs, then `f` has no size-3 circuit. -/
private theorem noSize3_of_frontier_false {f : (Fin 3 → Bool) → Bool}
    (mask : BitVec 8)
    (hf : ∀ bit (hbit : bit < 8),
      f (inputOfBit bit) = mask.getLsbD bit)
    (hfront : frontierCanOutput 2 mask = false) :
    ¬HasCircuitOfSize f 3 := by
  rintro ⟨⟨gates, out⟩, hc⟩
  match gates with
  | .cons (.cons (.cons .nil g0) g1) g2 =>
    have hmask : size3MaskFin g0 g1 g2 out = mask := by
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      rw [size3MaskFin_get g0 g1 g2 out _ hi, hc, hf _ hi]
    have hstate : containsState
        (state2 (gateEvalMask g0 inputMask)
          (gateEvalMask g1 (extendEnvMask inputMask (gateEvalMask g0 inputMask))))
        (frontier 2) = true := by
      simpa using state2_in_frontier g0 g1
    have hfinal : finalCanOutput (size3MaskFin g0 g1 g2 out)
        (state2 (gateEvalMask g0 inputMask)
          (gateEvalMask g1 (extendEnvMask inputMask (gateEvalMask g0 inputMask)))) = true := by
      simpa [size3MaskFin] using finalCanOutput_size3 g0 g1 g2 out
    have hfront' : frontierCanOutput 2 (size3MaskFin g0 g1 g2 out) = true :=
      any_of_containsState hstate hfinal
    rw [hmask] at hfront'
    rw [hfront] at hfront'
    cases hfront'

private theorem f_30_no_size3 : ¬HasCircuitOfSize Size3.Defs0.f_30 3 :=
  noSize3_of_frontier_false (f := Size3.Defs0.f_30) 0x1e#8
    (by
      intro bit hbit
      have hbit' : bit = 0 ∨ bit = 1 ∨ bit = 2 ∨ bit = 3 ∨
          bit = 4 ∨ bit = 5 ∨ bit = 6 ∨ bit = 7 := by omega
      rcases hbit' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [inputOfBit, inputMask, Size3.Defs0.f_30])
    f30_frontier_false

-- f_0: truth table 0x0 — size 1

def f_0_size : Nat := 1

def f_0_upper : HasCircuitOfSize Size3.Defs0.f_0 1 :=
  ⟨⟨gates![0 ∧ ¬0], mkRef 3 false⟩,
   by circuit_eval⟩

def f_0_lower : ∀ j, j < 1 → ¬HasCircuitOfSize Size3.Defs0.f_0 j := by
  intro j hj
  obtain rfl : j = 0 := by omega
  rw [hasSize0_iff]; decide

-- f_1: truth table 0x1 — size 2

def f_1_size : Nat := 2

def f_1_upper : HasCircuitOfSize Size3.Defs0.f_1 2 :=
  ⟨⟨gates![¬1 ∧ ¬0, 3 ∧ ¬2], mkRef 4 false⟩,
   by circuit_eval⟩

def f_1_lower : ∀ j, j < 2 → ¬HasCircuitOfSize Size3.Defs0.f_1 j := by
  intro j hj
  refine not_hasCircuitOfSize_of_le (k := 1) (by decide) (by omega) ?_
  rw [hasSize1_iff]; decide

-- f_3: truth table 0x3 — size 1

def f_3_size : Nat := 1

def f_3_upper : HasCircuitOfSize Size3.Defs0.f_3 1 :=
  ⟨⟨gates![¬2 ∧ ¬1], mkRef 3 false⟩,
   by circuit_eval⟩

def f_3_lower : ∀ j, j < 1 → ¬HasCircuitOfSize Size3.Defs0.f_3 j := by
  intro j hj
  obtain rfl : j = 0 := by omega
  rw [hasSize0_iff]; decide

-- f_6: truth table 0x6 — size 4

def f_6_size : Nat := 4

def f_6_upper : HasCircuitOfSize Size3.Defs0.f_6 4 :=
  ⟨⟨gates![¬1 ∧ 0, 1 ∧ ¬0, ¬4 ∧ ¬3, ¬5 ∧ ¬2], mkRef 6 false⟩,
   by circuit_eval⟩

def f_6_lower : ∀ j, j < 4 → ¬HasCircuitOfSize Size3.Defs0.f_6 j := by
  intro j hj
  if h : j ≤ 2 then
    exact not_hasCircuitOfSize_of_le (by decide) h
      (by rw [hasSize2_iff_canon]; decide)
  else
    obtain rfl : j = 3 := by omega
    exact noSize3_of_frontier_false (f := Size3.Defs0.f_6) 0x06#8
      (by
        intro bit hbit
        have hbit' : bit = 0 ∨ bit = 1 ∨ bit = 2 ∨ bit = 3 ∨
            bit = 4 ∨ bit = 5 ∨ bit = 6 ∨ bit = 7 := by omega
        rcases hbit' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [inputOfBit, inputMask, Size3.Defs0.f_6])
      (by rfl)

-- f_7: truth table 0x7 — size 2

def f_7_size : Nat := 2

def f_7_upper : HasCircuitOfSize Size3.Defs0.f_7 2 :=
  ⟨⟨gates![1 ∧ 0, ¬3 ∧ ¬2], mkRef 4 false⟩,
   by circuit_eval⟩

def f_7_lower : ∀ j, j < 2 → ¬HasCircuitOfSize Size3.Defs0.f_7 j := by
  intro j hj
  refine not_hasCircuitOfSize_of_le (k := 1) (by decide) (by omega) ?_
  rw [hasSize1_iff]; decide

-- f_15: truth table 0xf — size 0

def f_15_size : Nat := 0

def f_15_upper : HasCircuitOfSize Size3.Defs0.f_15 0 :=
  ⟨⟨gates![], mkRef 2 true⟩,
   by circuit_eval⟩

def f_15_lower : ∀ j, j < 0 → ¬HasCircuitOfSize Size3.Defs0.f_15 j :=
  fun _ h => absurd h (by omega)

-- f_22: truth table 0x16 — size 6

def f_22_size : Nat := 6

def f_22_upper : HasCircuitOfSize Size3.Defs0.f_22 6 :=
  ⟨⟨gates![2 ∧ 1,
           ¬2 ∧ ¬1,
           ¬3 ∧ ¬0,
           5 ∧ ¬4,
           4 ∧ 0,
           ¬7 ∧ ¬6], mkRef 8 true⟩,
   by circuit_eval⟩

def f_22_lower : ∀ j, j < 6 → ¬HasCircuitOfSize Size3.Defs0.f_22 j := by
  intro j hj
  if h : j ≤ 2 then
    exact not_hasCircuitOfSize_of_le (by decide) h
      (by rw [hasSize2_iff_canon]; decide)
  else
    have : j = 3 ∨ j = 4 ∨ j = 5 := by omega
    rcases this with rfl | rfl | rfl
    · exact noSize3_of_frontier_false (f := Size3.Defs0.f_22) 0x16#8
        (by
          intro bit hbit
          have hbit' : bit = 0 ∨ bit = 1 ∨ bit = 2 ∨ bit = 3 ∨
              bit = 4 ∨ bit = 5 ∨ bit = 6 ∨ bit = 7 := by omega
          rcases hbit' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            simp [inputOfBit, inputMask, Size3.Defs0.f_22])
        (by rfl)
    · sorry
    · sorry

-- f_23: truth table 0x17 — size 4

def f_23_size : Nat := 4

def f_23_upper : HasCircuitOfSize Size3.Defs0.f_23 4 :=
  ⟨⟨gates![2 ∧ 1, ¬2 ∧ ¬1, ¬4 ∧ 0, ¬5 ∧ ¬3], mkRef 6 false⟩,
   by circuit_eval⟩

def f_23_lower : ∀ j, j < 4 → ¬HasCircuitOfSize Size3.Defs0.f_23 j := by
  intro j hj
  if h : j ≤ 2 then
    exact not_hasCircuitOfSize_of_le (by decide) h
      (by rw [hasSize2_iff_canon]; decide)
  else
    obtain rfl : j = 3 := by omega
    exact noSize3_of_frontier_false (f := Size3.Defs0.f_23) 0x17#8
      (by
        intro bit hbit
        have hbit' : bit = 0 ∨ bit = 1 ∨ bit = 2 ∨ bit = 3 ∨
            bit = 4 ∨ bit = 5 ∨ bit = 6 ∨ bit = 7 := by omega
        rcases hbit' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [inputOfBit, inputMask, Size3.Defs0.f_23])
      (by rfl)

-- f_24: truth table 0x18 — size 5

def f_24_size : Nat := 5

def f_24_upper : HasCircuitOfSize Size3.Defs0.f_24 5 :=
  ⟨⟨gates![1 ∧ 0,
           3 ∧ ¬2,
           ¬1 ∧ ¬0,
           5 ∧ 2,
           ¬6 ∧ ¬4], mkRef 7 true⟩,
   by circuit_eval⟩

def f_24_lower : ∀ j, j < 5 → ¬HasCircuitOfSize Size3.Defs0.f_24 j := by
  intro j hj
  if h : j ≤ 2 then
    exact not_hasCircuitOfSize_of_le (by decide) h
      (by rw [hasSize2_iff_canon]; decide)
  else
    have : j = 3 ∨ j = 4 := by omega
    rcases this with rfl | rfl
    · exact noSize3_of_frontier_false (f := Size3.Defs0.f_24) 0x18#8
        (by
          intro bit hbit
          have hbit' : bit = 0 ∨ bit = 1 ∨ bit = 2 ∨ bit = 3 ∨
              bit = 4 ∨ bit = 5 ∨ bit = 6 ∨ bit = 7 := by omega
          rcases hbit' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            simp [inputOfBit, inputMask, Size3.Defs0.f_24])
        (by rfl)
    · sorry

-- f_25: truth table 0x19 — size 4

def f_25_size : Nat := 4

def f_25_upper : HasCircuitOfSize Size3.Defs0.f_25 4 :=
  ⟨⟨gates![1 ∧ 0, 3 ∧ ¬2, ¬1 ∧ ¬0, ¬5 ∧ ¬4], mkRef 6 true⟩,
   by circuit_eval⟩

def f_25_lower : ∀ j, j < 4 → ¬HasCircuitOfSize Size3.Defs0.f_25 j := by
  intro j hj
  if h : j ≤ 2 then
    exact not_hasCircuitOfSize_of_le (by decide) h
      (by rw [hasSize2_iff_canon]; decide)
  else
    obtain rfl : j = 3 := by omega
    exact noSize3_of_frontier_false (f := Size3.Defs0.f_25) 0x19#8
      (by
        intro bit hbit
        have hbit' : bit = 0 ∨ bit = 1 ∨ bit = 2 ∨ bit = 3 ∨
            bit = 4 ∨ bit = 5 ∨ bit = 6 ∨ bit = 7 := by omega
        rcases hbit' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [inputOfBit, inputMask, Size3.Defs0.f_25])
      (by rfl)

-- f_27: truth table 0x1b — size 3

def f_27_size : Nat := 3

def f_27_upper : HasCircuitOfSize Size3.Defs0.f_27 3 :=
  ⟨⟨gates![2 ∧ 0, 1 ∧ ¬0, ¬4 ∧ ¬3], mkRef 5 false⟩,
   by circuit_eval⟩

def f_27_lower : ∀ j, j < 3 → ¬HasCircuitOfSize Size3.Defs0.f_27 j := by
  intro j hj
  exact noCircuitOfSize_of_inputMinor
    (f := Size3.Defs0.f_27) (g := Size2.Defs0.f_6)
    f_27_xorMinor
    (by
      intro input
      simp [f_27_xorMinor, Size2.Defs0.f_6, Size3.Defs0.f_27, Ref.eval])
    (Size2.Proofs0.f_6_lower j hj)

-- f_30: truth table 0x1e — size 4

def f_30_size : Nat := 4

def f_30_upper : HasCircuitOfSize Size3.Defs0.f_30 4 :=
  ⟨⟨gates![¬1 ∧ ¬0, ¬3 ∧ 2, 3 ∧ ¬2, ¬5 ∧ ¬4], mkRef 6 false⟩,
   by circuit_eval⟩

def f_30_lower : ∀ j, j < 4 → ¬HasCircuitOfSize Size3.Defs0.f_30 j := by
  intro j hj
  if h : j ≤ 2 then
    exact not_hasCircuitOfSize_of_le (by decide) h
      (by rw [hasSize2_iff_canon]; decide)
  else
    obtain rfl : j = 3 := by omega
    exact f_30_no_size3

-- f_60: truth table 0x3c — size 3

def f_60_size : Nat := 3

def f_60_upper : HasCircuitOfSize Size3.Defs0.f_60 3 :=
  ⟨⟨gates![¬2 ∧ 1, 2 ∧ ¬1, ¬4 ∧ ¬3], mkRef 5 true⟩,
   by circuit_eval⟩

def f_60_lower : ∀ j, j < 3 → ¬HasCircuitOfSize Size3.Defs0.f_60 j := by
  intro j hj
  exact noCircuitOfSize_of_inputMinor
    (f := Size3.Defs0.f_60) (g := Size2.Defs0.f_6)
    f_60_xorMinor
    (by
      intro input
      simp [f_60_xorMinor, Size2.Defs0.f_6, Size3.Defs0.f_60, Ref.eval])
    (Size2.Proofs0.f_6_lower j hj)

-- f_105: truth table 0x69 — size 6

def f_105_size : Nat := 6

def f_105_upper : HasCircuitOfSize Size3.Defs0.f_105 6 :=
  ⟨⟨gates![¬2 ∧ ¬1,
           2 ∧ 1,
           ¬4 ∧ ¬3,
           5 ∧ 0,
           ¬5 ∧ ¬0,
           ¬7 ∧ ¬6], mkRef 8 true⟩,
   by circuit_eval⟩

def f_105_lower : ∀ j, j < 6 → ¬HasCircuitOfSize Size3.Defs0.f_105 j := by
  intro j hj
  if h : j ≤ 2 then
    exact not_hasCircuitOfSize_of_le (by decide) h
      (by rw [hasSize2_iff_canon]; decide)
  else
    have : j = 3 ∨ j = 4 ∨ j = 5 := by omega
    rcases this with rfl | rfl | rfl
    · exact noSize3_of_frontier_false (f := Size3.Defs0.f_105) 0x69#8
        (by
          intro bit hbit
          have hbit' : bit = 0 ∨ bit = 1 ∨ bit = 2 ∨ bit = 3 ∨
              bit = 4 ∨ bit = 5 ∨ bit = 6 ∨ bit = 7 := by omega
          rcases hbit' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            simp [inputOfBit, inputMask, Size3.Defs0.f_105])
        (by rfl)
    · sorry
    · sorry

end Size3.Proofs0
