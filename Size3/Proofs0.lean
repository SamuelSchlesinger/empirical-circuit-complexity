import Std.Tactic.BVDecide
import Circuits.Basic
import Size3.Defs0

namespace Size3.Proofs0

open Circuits

-- f_0: truth table 0x0 — size 1

def f_0_size : Nat := 1

def f_0_upper : HasCircuitOfSize Size3.Defs0.f_0 1 :=
  ⟨⟨.cons .nil ⟨⟨⟨0, by omega⟩, false⟩, ⟨⟨0, by omega⟩, true⟩⟩, ⟨⟨3, by omega⟩, false⟩⟩,
   fun input => by
     have h0 : Nat.add 3 0 = 3 := rfl
     simp only [h0, Circuit.eval, Ref.eval, GateList.eval, Gate.eval, extendEnv, Size3.Defs0.f_0]
     bv_decide
  ⟩

def f_0_lower : ∀ j, j < 1 → ¬HasCircuitOfSize Size3.Defs0.f_0 j := by
  sorry

-- f_1: truth table 0x1 — size 2

def f_1_size : Nat := 2

def f_1_upper : HasCircuitOfSize Size3.Defs0.f_1 2 :=
  ⟨⟨.cons (.cons .nil ⟨⟨⟨1, by omega⟩, true⟩, ⟨⟨0, by omega⟩, true⟩⟩) ⟨⟨⟨3, by omega⟩, false⟩, ⟨⟨2, by omega⟩, true⟩⟩, ⟨⟨4, by omega⟩, false⟩⟩,
   fun input => by
     have h0 : Nat.add 3 0 = 3 := rfl
     have h1 : Nat.add 3 1 = 4 := rfl
     simp only [h0, h1, Circuit.eval, Ref.eval, GateList.eval, Gate.eval, extendEnv, Size3.Defs0.f_1]
     bv_decide
  ⟩

def f_1_lower : ∀ j, j < 2 → ¬HasCircuitOfSize Size3.Defs0.f_1 j := by
  sorry

-- f_3: truth table 0x3 — size 1

def f_3_size : Nat := 1

def f_3_upper : HasCircuitOfSize Size3.Defs0.f_3 1 :=
  ⟨⟨.cons .nil ⟨⟨⟨2, by omega⟩, true⟩, ⟨⟨1, by omega⟩, true⟩⟩, ⟨⟨3, by omega⟩, false⟩⟩,
   fun input => by
     have h0 : Nat.add 3 0 = 3 := rfl
     simp only [h0, Circuit.eval, Ref.eval, GateList.eval, Gate.eval, extendEnv, Size3.Defs0.f_3]
     bv_decide
  ⟩

def f_3_lower : ∀ j, j < 1 → ¬HasCircuitOfSize Size3.Defs0.f_3 j := by
  sorry

-- f_6: truth table 0x6 — size 4

def f_6_size : Nat := 4

def f_6_upper : HasCircuitOfSize Size3.Defs0.f_6 4 :=
  ⟨⟨.cons (.cons (.cons (.cons .nil ⟨⟨⟨1, by omega⟩, true⟩, ⟨⟨0, by omega⟩, false⟩⟩) ⟨⟨⟨1, by omega⟩, false⟩, ⟨⟨0, by omega⟩, true⟩⟩) ⟨⟨⟨4, by omega⟩, true⟩, ⟨⟨3, by omega⟩, true⟩⟩) ⟨⟨⟨5, by omega⟩, true⟩, ⟨⟨2, by omega⟩, true⟩⟩, ⟨⟨6, by omega⟩, false⟩⟩,
   fun input => by
     have h0 : Nat.add 3 0 = 3 := rfl
     have h1 : Nat.add 3 1 = 4 := rfl
     have h2 : Nat.add 3 2 = 5 := rfl
     have h3 : Nat.add 3 3 = 6 := rfl
     simp only [h0, h1, h2, h3, Circuit.eval, Ref.eval, GateList.eval, Gate.eval, extendEnv, Size3.Defs0.f_6]
     bv_decide
  ⟩

def f_6_lower : ∀ j, j < 4 → ¬HasCircuitOfSize Size3.Defs0.f_6 j := by
  sorry

-- f_7: truth table 0x7 — size 2

def f_7_size : Nat := 2

def f_7_upper : HasCircuitOfSize Size3.Defs0.f_7 2 :=
  ⟨⟨.cons (.cons .nil ⟨⟨⟨1, by omega⟩, false⟩, ⟨⟨0, by omega⟩, false⟩⟩) ⟨⟨⟨3, by omega⟩, true⟩, ⟨⟨2, by omega⟩, true⟩⟩, ⟨⟨4, by omega⟩, false⟩⟩,
   fun input => by
     have h0 : Nat.add 3 0 = 3 := rfl
     have h1 : Nat.add 3 1 = 4 := rfl
     simp only [h0, h1, Circuit.eval, Ref.eval, GateList.eval, Gate.eval, extendEnv, Size3.Defs0.f_7]
     bv_decide
  ⟩

def f_7_lower : ∀ j, j < 2 → ¬HasCircuitOfSize Size3.Defs0.f_7 j := by
  sorry

-- f_15: truth table 0xf — size 0

def f_15_size : Nat := 0

def f_15_upper : HasCircuitOfSize Size3.Defs0.f_15 0 :=
  ⟨⟨.nil, ⟨⟨2, by omega⟩, true⟩⟩,
   fun input => by
     simp only [Circuit.eval, Ref.eval, GateList.eval, Gate.eval, extendEnv, Size3.Defs0.f_15]
     bv_decide
  ⟩

def f_15_lower : ∀ j, j < 0 → ¬HasCircuitOfSize Size3.Defs0.f_15 j := by
  sorry

-- f_22: truth table 0x16 — size 6

def f_22_size : Nat := 6

def f_22_upper : HasCircuitOfSize Size3.Defs0.f_22 6 :=
  ⟨⟨.cons (.cons (.cons (.cons (.cons (.cons .nil ⟨⟨⟨2, by omega⟩, false⟩, ⟨⟨1, by omega⟩, false⟩⟩) ⟨⟨⟨2, by omega⟩, true⟩, ⟨⟨1, by omega⟩, true⟩⟩) ⟨⟨⟨3, by omega⟩, true⟩, ⟨⟨0, by omega⟩, true⟩⟩) ⟨⟨⟨5, by omega⟩, false⟩, ⟨⟨4, by omega⟩, true⟩⟩) ⟨⟨⟨4, by omega⟩, false⟩, ⟨⟨0, by omega⟩, false⟩⟩) ⟨⟨⟨7, by omega⟩, true⟩, ⟨⟨6, by omega⟩, true⟩⟩, ⟨⟨8, by omega⟩, true⟩⟩,
   fun input => by
     have h0 : Nat.add 3 0 = 3 := rfl
     have h1 : Nat.add 3 1 = 4 := rfl
     have h2 : Nat.add 3 2 = 5 := rfl
     have h3 : Nat.add 3 3 = 6 := rfl
     have h4 : Nat.add 3 4 = 7 := rfl
     have h5 : Nat.add 3 5 = 8 := rfl
     simp only [h0, h1, h2, h3, h4, h5, Circuit.eval, Ref.eval, GateList.eval, Gate.eval, extendEnv, Size3.Defs0.f_22]
     bv_decide
  ⟩

def f_22_lower : ∀ j, j < 6 → ¬HasCircuitOfSize Size3.Defs0.f_22 j := by
  sorry

-- f_23: truth table 0x17 — size 4

def f_23_size : Nat := 4

def f_23_upper : HasCircuitOfSize Size3.Defs0.f_23 4 :=
  ⟨⟨.cons (.cons (.cons (.cons .nil ⟨⟨⟨2, by omega⟩, false⟩, ⟨⟨1, by omega⟩, false⟩⟩) ⟨⟨⟨2, by omega⟩, true⟩, ⟨⟨1, by omega⟩, true⟩⟩) ⟨⟨⟨4, by omega⟩, true⟩, ⟨⟨0, by omega⟩, false⟩⟩) ⟨⟨⟨5, by omega⟩, true⟩, ⟨⟨3, by omega⟩, true⟩⟩, ⟨⟨6, by omega⟩, false⟩⟩,
   fun input => by
     have h0 : Nat.add 3 0 = 3 := rfl
     have h1 : Nat.add 3 1 = 4 := rfl
     have h2 : Nat.add 3 2 = 5 := rfl
     have h3 : Nat.add 3 3 = 6 := rfl
     simp only [h0, h1, h2, h3, Circuit.eval, Ref.eval, GateList.eval, Gate.eval, extendEnv, Size3.Defs0.f_23]
     bv_decide
  ⟩

def f_23_lower : ∀ j, j < 4 → ¬HasCircuitOfSize Size3.Defs0.f_23 j := by
  sorry

-- f_24: truth table 0x18 — size 5

def f_24_size : Nat := 5

def f_24_upper : HasCircuitOfSize Size3.Defs0.f_24 5 :=
  ⟨⟨.cons (.cons (.cons (.cons (.cons .nil ⟨⟨⟨1, by omega⟩, false⟩, ⟨⟨0, by omega⟩, false⟩⟩) ⟨⟨⟨3, by omega⟩, false⟩, ⟨⟨2, by omega⟩, true⟩⟩) ⟨⟨⟨1, by omega⟩, true⟩, ⟨⟨0, by omega⟩, true⟩⟩) ⟨⟨⟨5, by omega⟩, false⟩, ⟨⟨2, by omega⟩, false⟩⟩) ⟨⟨⟨6, by omega⟩, true⟩, ⟨⟨4, by omega⟩, true⟩⟩, ⟨⟨7, by omega⟩, true⟩⟩,
   fun input => by
     have h0 : Nat.add 3 0 = 3 := rfl
     have h1 : Nat.add 3 1 = 4 := rfl
     have h2 : Nat.add 3 2 = 5 := rfl
     have h3 : Nat.add 3 3 = 6 := rfl
     have h4 : Nat.add 3 4 = 7 := rfl
     simp only [h0, h1, h2, h3, h4, Circuit.eval, Ref.eval, GateList.eval, Gate.eval, extendEnv, Size3.Defs0.f_24]
     bv_decide
  ⟩

def f_24_lower : ∀ j, j < 5 → ¬HasCircuitOfSize Size3.Defs0.f_24 j := by
  sorry

-- f_25: truth table 0x19 — size 4

def f_25_size : Nat := 4

def f_25_upper : HasCircuitOfSize Size3.Defs0.f_25 4 :=
  ⟨⟨.cons (.cons (.cons (.cons .nil ⟨⟨⟨1, by omega⟩, false⟩, ⟨⟨0, by omega⟩, false⟩⟩) ⟨⟨⟨3, by omega⟩, false⟩, ⟨⟨2, by omega⟩, true⟩⟩) ⟨⟨⟨1, by omega⟩, true⟩, ⟨⟨0, by omega⟩, true⟩⟩) ⟨⟨⟨5, by omega⟩, true⟩, ⟨⟨4, by omega⟩, true⟩⟩, ⟨⟨6, by omega⟩, true⟩⟩,
   fun input => by
     have h0 : Nat.add 3 0 = 3 := rfl
     have h1 : Nat.add 3 1 = 4 := rfl
     have h2 : Nat.add 3 2 = 5 := rfl
     have h3 : Nat.add 3 3 = 6 := rfl
     simp only [h0, h1, h2, h3, Circuit.eval, Ref.eval, GateList.eval, Gate.eval, extendEnv, Size3.Defs0.f_25]
     bv_decide
  ⟩

def f_25_lower : ∀ j, j < 4 → ¬HasCircuitOfSize Size3.Defs0.f_25 j := by
  sorry

-- f_27: truth table 0x1b — size 3

def f_27_size : Nat := 3

def f_27_upper : HasCircuitOfSize Size3.Defs0.f_27 3 :=
  ⟨⟨.cons (.cons (.cons .nil ⟨⟨⟨2, by omega⟩, false⟩, ⟨⟨0, by omega⟩, false⟩⟩) ⟨⟨⟨1, by omega⟩, false⟩, ⟨⟨0, by omega⟩, true⟩⟩) ⟨⟨⟨4, by omega⟩, true⟩, ⟨⟨3, by omega⟩, true⟩⟩, ⟨⟨5, by omega⟩, false⟩⟩,
   fun input => by
     have h0 : Nat.add 3 0 = 3 := rfl
     have h1 : Nat.add 3 1 = 4 := rfl
     have h2 : Nat.add 3 2 = 5 := rfl
     simp only [h0, h1, h2, Circuit.eval, Ref.eval, GateList.eval, Gate.eval, extendEnv, Size3.Defs0.f_27]
     bv_decide
  ⟩

def f_27_lower : ∀ j, j < 3 → ¬HasCircuitOfSize Size3.Defs0.f_27 j := by
  sorry

-- f_30: truth table 0x1e — size 4

def f_30_size : Nat := 4

def f_30_upper : HasCircuitOfSize Size3.Defs0.f_30 4 :=
  ⟨⟨.cons (.cons (.cons (.cons .nil ⟨⟨⟨1, by omega⟩, true⟩, ⟨⟨0, by omega⟩, true⟩⟩) ⟨⟨⟨3, by omega⟩, true⟩, ⟨⟨2, by omega⟩, false⟩⟩) ⟨⟨⟨3, by omega⟩, false⟩, ⟨⟨2, by omega⟩, true⟩⟩) ⟨⟨⟨5, by omega⟩, true⟩, ⟨⟨4, by omega⟩, true⟩⟩, ⟨⟨6, by omega⟩, false⟩⟩,
   fun input => by
     have h0 : Nat.add 3 0 = 3 := rfl
     have h1 : Nat.add 3 1 = 4 := rfl
     have h2 : Nat.add 3 2 = 5 := rfl
     have h3 : Nat.add 3 3 = 6 := rfl
     simp only [h0, h1, h2, h3, Circuit.eval, Ref.eval, GateList.eval, Gate.eval, extendEnv, Size3.Defs0.f_30]
     bv_decide
  ⟩

def f_30_lower : ∀ j, j < 4 → ¬HasCircuitOfSize Size3.Defs0.f_30 j := by
  sorry

-- f_60: truth table 0x3c — size 3

def f_60_size : Nat := 3

def f_60_upper : HasCircuitOfSize Size3.Defs0.f_60 3 :=
  ⟨⟨.cons (.cons (.cons .nil ⟨⟨⟨2, by omega⟩, true⟩, ⟨⟨1, by omega⟩, false⟩⟩) ⟨⟨⟨2, by omega⟩, false⟩, ⟨⟨1, by omega⟩, true⟩⟩) ⟨⟨⟨4, by omega⟩, true⟩, ⟨⟨3, by omega⟩, true⟩⟩, ⟨⟨5, by omega⟩, true⟩⟩,
   fun input => by
     have h0 : Nat.add 3 0 = 3 := rfl
     have h1 : Nat.add 3 1 = 4 := rfl
     have h2 : Nat.add 3 2 = 5 := rfl
     simp only [h0, h1, h2, Circuit.eval, Ref.eval, GateList.eval, Gate.eval, extendEnv, Size3.Defs0.f_60]
     bv_decide
  ⟩

def f_60_lower : ∀ j, j < 3 → ¬HasCircuitOfSize Size3.Defs0.f_60 j := by
  sorry

-- f_105: truth table 0x69 — size 6

def f_105_size : Nat := 6

def f_105_upper : HasCircuitOfSize Size3.Defs0.f_105 6 :=
  ⟨⟨.cons (.cons (.cons (.cons (.cons (.cons .nil ⟨⟨⟨2, by omega⟩, true⟩, ⟨⟨1, by omega⟩, true⟩⟩) ⟨⟨⟨2, by omega⟩, false⟩, ⟨⟨1, by omega⟩, false⟩⟩) ⟨⟨⟨4, by omega⟩, true⟩, ⟨⟨3, by omega⟩, true⟩⟩) ⟨⟨⟨5, by omega⟩, false⟩, ⟨⟨0, by omega⟩, false⟩⟩) ⟨⟨⟨5, by omega⟩, true⟩, ⟨⟨0, by omega⟩, true⟩⟩) ⟨⟨⟨7, by omega⟩, true⟩, ⟨⟨6, by omega⟩, true⟩⟩, ⟨⟨8, by omega⟩, true⟩⟩,
   fun input => by
     have h0 : Nat.add 3 0 = 3 := rfl
     have h1 : Nat.add 3 1 = 4 := rfl
     have h2 : Nat.add 3 2 = 5 := rfl
     have h3 : Nat.add 3 3 = 6 := rfl
     have h4 : Nat.add 3 4 = 7 := rfl
     have h5 : Nat.add 3 5 = 8 := rfl
     simp only [h0, h1, h2, h3, h4, h5, Circuit.eval, Ref.eval, GateList.eval, Gate.eval, extendEnv, Size3.Defs0.f_105]
     bv_decide
  ⟩

def f_105_lower : ∀ j, j < 6 → ¬HasCircuitOfSize Size3.Defs0.f_105 j := by
  sorry

end Size3.Proofs0
