import Std.Tactic.BVDecide
import Circuits.Basic
import Size3.Defs0

namespace Size3.Proofs0

open Circuits

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
  sorry

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
  sorry

-- f_7: truth table 0x7 — size 2

def f_7_size : Nat := 2

def f_7_upper : HasCircuitOfSize Size3.Defs0.f_7 2 :=
  ⟨⟨gates![1 ∧ 0, ¬3 ∧ ¬2], mkRef 4 false⟩,
   by circuit_eval⟩

def f_7_lower : ∀ j, j < 2 → ¬HasCircuitOfSize Size3.Defs0.f_7 j := by
  sorry

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
  sorry

-- f_23: truth table 0x17 — size 4

def f_23_size : Nat := 4

def f_23_upper : HasCircuitOfSize Size3.Defs0.f_23 4 :=
  ⟨⟨gates![2 ∧ 1, ¬2 ∧ ¬1, ¬4 ∧ 0, ¬5 ∧ ¬3], mkRef 6 false⟩,
   by circuit_eval⟩

def f_23_lower : ∀ j, j < 4 → ¬HasCircuitOfSize Size3.Defs0.f_23 j := by
  sorry

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
  sorry

-- f_25: truth table 0x19 — size 4

def f_25_size : Nat := 4

def f_25_upper : HasCircuitOfSize Size3.Defs0.f_25 4 :=
  ⟨⟨gates![1 ∧ 0, 3 ∧ ¬2, ¬1 ∧ ¬0, ¬5 ∧ ¬4], mkRef 6 true⟩,
   by circuit_eval⟩

def f_25_lower : ∀ j, j < 4 → ¬HasCircuitOfSize Size3.Defs0.f_25 j := by
  sorry

-- f_27: truth table 0x1b — size 3

def f_27_size : Nat := 3

def f_27_upper : HasCircuitOfSize Size3.Defs0.f_27 3 :=
  ⟨⟨gates![2 ∧ 0, 1 ∧ ¬0, ¬4 ∧ ¬3], mkRef 5 false⟩,
   by circuit_eval⟩

def f_27_lower : ∀ j, j < 3 → ¬HasCircuitOfSize Size3.Defs0.f_27 j := by
  sorry

-- f_30: truth table 0x1e — size 4

def f_30_size : Nat := 4

def f_30_upper : HasCircuitOfSize Size3.Defs0.f_30 4 :=
  ⟨⟨gates![¬1 ∧ ¬0, ¬3 ∧ 2, 3 ∧ ¬2, ¬5 ∧ ¬4], mkRef 6 false⟩,
   by circuit_eval⟩

def f_30_lower : ∀ j, j < 4 → ¬HasCircuitOfSize Size3.Defs0.f_30 j := by
  sorry

-- f_60: truth table 0x3c — size 3

def f_60_size : Nat := 3

def f_60_upper : HasCircuitOfSize Size3.Defs0.f_60 3 :=
  ⟨⟨gates![¬2 ∧ 1, 2 ∧ ¬1, ¬4 ∧ ¬3], mkRef 5 true⟩,
   by circuit_eval⟩

def f_60_lower : ∀ j, j < 3 → ¬HasCircuitOfSize Size3.Defs0.f_60 j := by
  sorry

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
  sorry

end Size3.Proofs0
