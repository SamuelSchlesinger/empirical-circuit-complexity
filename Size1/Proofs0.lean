import Std.Tactic.BVDecide
import Circuits.Basic
import Size1.Defs0

namespace Size1.Proofs0

open Circuits

-- f_0: constant false — complexity 1

def f_0_size : Nat := 1

def f_0_upper : HasCircuitOfSize Size1.Defs0.f_0 1 :=
  ⟨⟨gates![0 ∧ ¬0], mkRef 1 false⟩,
   by circuit_eval⟩

def f_0_lower : ∀ j, j < 1 → ¬HasCircuitOfSize Size1.Defs0.f_0 j := by
  intro j hj
  obtain rfl : j = 0 := by omega
  rw [hasSize0_iff]; decide

-- f_1: ¬x₀ — complexity 0

def f_1_size : Nat := 0

def f_1_upper : HasCircuitOfSize Size1.Defs0.f_1 0 :=
  ⟨⟨gates![], mkRef 0 true⟩,
   by circuit_eval⟩

def f_1_lower : ∀ j, j < 0 → ¬HasCircuitOfSize Size1.Defs0.f_1 j :=
  fun _ h => absurd h (by omega)

end Size1.Proofs0
