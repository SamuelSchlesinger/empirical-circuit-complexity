import Std.Tactic.BVDecide
import Circuits.Basic
import Size2.Defs0

namespace Size2.Proofs0

open Circuits

-- f_0: truth table 0x0 — size 1

def f_0_size : Nat := 1

def f_0_upper : HasCircuitOfSize Size2.Defs0.f_0 1 :=
  ⟨⟨.cons .nil ⟨⟨⟨0, by omega⟩, false⟩, ⟨⟨0, by omega⟩, true⟩⟩, ⟨⟨2, by omega⟩, false⟩⟩,
   fun input => by
     have h0 : Nat.add 2 0 = 2 := rfl
     simp only [h0, Circuit.eval, Ref.eval, GateList.eval, Gate.eval, extendEnv, Size2.Defs0.f_0]
     bv_decide
  ⟩

def f_0_lower : ∀ j, j < 1 → ¬HasCircuitOfSize Size2.Defs0.f_0 j := by
  sorry

-- f_1: truth table 0x1 — size 1

def f_1_size : Nat := 1

def f_1_upper : HasCircuitOfSize Size2.Defs0.f_1 1 :=
  ⟨⟨.cons .nil ⟨⟨⟨1, by omega⟩, true⟩, ⟨⟨0, by omega⟩, true⟩⟩, ⟨⟨2, by omega⟩, false⟩⟩,
   fun input => by
     have h0 : Nat.add 2 0 = 2 := rfl
     simp only [h0, Circuit.eval, Ref.eval, GateList.eval, Gate.eval, extendEnv, Size2.Defs0.f_1]
     bv_decide
  ⟩

def f_1_lower : ∀ j, j < 1 → ¬HasCircuitOfSize Size2.Defs0.f_1 j := by
  sorry

-- f_3: truth table 0x3 — size 0

def f_3_size : Nat := 0

def f_3_upper : HasCircuitOfSize Size2.Defs0.f_3 0 :=
  ⟨⟨.nil, ⟨⟨1, by omega⟩, true⟩⟩,
   fun input => by
     simp only [Circuit.eval, Ref.eval, GateList.eval, Gate.eval, extendEnv, Size2.Defs0.f_3]
     bv_decide
  ⟩

def f_3_lower : ∀ j, j < 0 → ¬HasCircuitOfSize Size2.Defs0.f_3 j := by
  sorry

-- f_6: truth table 0x6 — size 3

def f_6_size : Nat := 3

def f_6_upper : HasCircuitOfSize Size2.Defs0.f_6 3 :=
  ⟨⟨.cons (.cons (.cons .nil ⟨⟨⟨1, by omega⟩, true⟩, ⟨⟨0, by omega⟩, false⟩⟩) ⟨⟨⟨1, by omega⟩, false⟩, ⟨⟨0, by omega⟩, true⟩⟩) ⟨⟨⟨3, by omega⟩, true⟩, ⟨⟨2, by omega⟩, true⟩⟩, ⟨⟨4, by omega⟩, true⟩⟩,
   fun input => by
     have h0 : Nat.add 2 0 = 2 := rfl
     have h1 : Nat.add 2 1 = 3 := rfl
     have h2 : Nat.add 2 2 = 4 := rfl
     simp only [h0, h1, h2, Circuit.eval, Ref.eval, GateList.eval, Gate.eval, extendEnv, Size2.Defs0.f_6]
     bv_decide
  ⟩

def f_6_lower : ∀ j, j < 3 → ¬HasCircuitOfSize Size2.Defs0.f_6 j := by
  sorry

end Size2.Proofs0
