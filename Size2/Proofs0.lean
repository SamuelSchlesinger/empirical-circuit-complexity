import Std.Tactic.BVDecide
import Circuits.Basic
import Size2.Defs0

namespace Size2.Proofs0

open Circuits

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

def f_6_lower : ∀ j, j < 3 → ¬HasCircuitOfSize Size2.Defs0.f_6 j := by
  sorry

end Size2.Proofs0
