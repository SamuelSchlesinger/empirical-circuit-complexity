import Std.Tactic.BVDecide
import Circuits.Basic
import Size2.Defs0

set_option maxHeartbeats 4000000

namespace Size2.Proofs0

open Circuits

-- Simp helpers: Fin coercion/val should reduce to Nat.
@[simp] private theorem fin_val_mk {n m : Nat} (h : n < m) :
    (⟨n, h⟩ : Fin m).val = n := rfl

-- Match the ↑ coercion head symbol (Coe.coe, not Fin.val).
@[simp] private theorem fin_coe_to_nat {m n : Nat} (h : n < m) :
    (↑(⟨n, h⟩ : Fin m) : Nat) = n := rfl

-- f_0: truth table 0x0 — size 1

def f_0_size : Nat := 1

def f_0_upper : HasCircuitOfSize Size2.Defs0.f_0 1 :=
  ⟨⟨gates![0 ∧ ¬0], mkRef 2 false⟩,
   by circuit_eval⟩

def f_0_lower : ∀ j, j < 1 → ¬HasCircuitOfSize Size2.Defs0.f_0 j := by
  intro j hj
  obtain rfl : j = 0 := by omega
  rw [hasSize0_iff]; decide

-- f_1: truth table 0x1 — size 1

def f_1_size : Nat := 1

def f_1_upper : HasCircuitOfSize Size2.Defs0.f_1 1 :=
  ⟨⟨gates![¬1 ∧ ¬0], mkRef 2 false⟩,
   by circuit_eval⟩

def f_1_lower : ∀ j, j < 1 → ¬HasCircuitOfSize Size2.Defs0.f_1 j := by
  intro j hj
  obtain rfl : j = 0 := by omega
  rw [hasSize0_iff]; decide

-- f_3: truth table 0x3 — size 0

def f_3_size : Nat := 0

def f_3_upper : HasCircuitOfSize Size2.Defs0.f_3 0 :=
  ⟨⟨gates![], mkRef 1 true⟩,
   by circuit_eval⟩

def f_3_lower : ∀ j, j < 0 → ¬HasCircuitOfSize Size2.Defs0.f_3 j :=
  fun _ h => absurd h (by omega)

-- f_6: truth table 0x6 — size 3

def f_6_size : Nat := 3

def f_6_upper : HasCircuitOfSize Size2.Defs0.f_6 3 :=
  ⟨⟨gates![¬1 ∧ 0, 1 ∧ ¬0, ¬3 ∧ ¬2], mkRef 4 true⟩,
   by circuit_eval⟩

-- Lower bound: XOR requires at least 3 gates.
-- Full exhaustive case analysis over all circuit parameters.
def f_6_lower : ∀ j, j < 3 → ¬HasCircuitOfSize Size2.Defs0.f_6 j := by
  intro j hj
  have hj3 : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases hj3 with rfl | rfl | rfl
  · -- j = 0
    exact no_size0_of_constant (by simp [Size2.Defs0.f_6])
  · -- j = 1
    intro ⟨⟨gates, outref⟩, hc⟩
    match gates with
    | .cons .nil gate =>
      obtain ⟨⟨⟨li, hli⟩, ln⟩, ⟨⟨ri, hri⟩, rn⟩⟩ := gate
      obtain ⟨⟨oi, hoi⟩, on_⟩ := outref
      cases ln <;> cases rn <;> cases on_ <;> (
        have hli' : li = 0 ∨ li = 1 := by omega
        have hri' : ri = 0 ∨ ri = 1 := by omega
        have hoi' : oi = 0 ∨ oi = 1 ∨ oi = 2 := by omega
        rcases hli' with rfl | rfl <;> rcases hri' with rfl | rfl <;>
          rcases hoi' with rfl | rfl | rfl <;> (
            have h1 := hc (fun _ => false)
            have h2 := hc (fun i : Fin 2 => if i.val = 0 then true else false)
            have h3 := hc (fun i : Fin 2 => if i.val = 0 then false else true)
            have h4 := hc (fun _ => true)
            simp [Circuit.eval, Ref.eval, GateList.eval, Gate.eval, extendEnv,
                  Size2.Defs0.f_6] at h1 h2 h3 h4))
  · -- j = 2: exhaustive case analysis over all circuit parameters
    intro ⟨⟨gates, outref⟩, hc⟩
    match gates with
    | .cons (.cons .nil gate0) gate1 =>
      obtain ⟨⟨o, ho⟩, on_⟩ := outref
      obtain ⟨⟨⟨l1, hl1⟩, n1l⟩, ⟨⟨r1, hr1⟩, n1r⟩⟩ := gate1
      obtain ⟨⟨⟨gl, hgl⟩, gln⟩, ⟨⟨gr, hgr⟩, grn⟩⟩ := gate0
      have ho' : o = 0 ∨ o = 1 ∨ o = 2 ∨ o = 3 := by omega
      have hl1' : l1 = 0 ∨ l1 = 1 ∨ l1 = 2 := by omega
      have hr1' : r1 = 0 ∨ r1 = 1 ∨ r1 = 2 := by omega
      have hgl' : gl = 0 ∨ gl = 1 := by omega
      have hgr' : gr = 0 ∨ gr = 1 := by omega
      rcases ho' with rfl | rfl | rfl | rfl <;>
        rcases hl1' with rfl | rfl | rfl <;>
        rcases hr1' with rfl | rfl | rfl <;>
        rcases hgl' with rfl | rfl <;>
        rcases hgr' with rfl | rfl <;>
        cases n1l <;> cases n1r <;> cases on_ <;> cases gln <;> cases grn <;> (
          have h1 := hc (fun _ => false)
          have h2 := hc (fun i : Fin 2 => if i.val = 0 then true else false)
          have h3 := hc (fun i : Fin 2 => if i.val = 0 then false else true)
          have h4 := hc (fun _ => true)
          simp [Circuit.eval, Ref.eval, GateList.eval, Gate.eval, extendEnv,
                Size2.Defs0.f_6] at h1 h2 h3 h4
          try omega)

end Size2.Proofs0
