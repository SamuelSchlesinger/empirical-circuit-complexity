import Circuits.Basic
import Size1.Defs0

namespace Size1.Proofs0

open Circuits

-- f_0: constant false — complexity 1

def f_0_size : Nat := 1

def f_0_upper : HasCircuitOfSize Size1.Defs0.f_0 1 :=
  ⟨⟨.cons .nil ⟨⟨⟨0, by omega⟩, false⟩, ⟨⟨0, by omega⟩, true⟩⟩,
    ⟨⟨1, by omega⟩, false⟩⟩,
   fun input => by
     simp [Circuit.eval, Ref.eval, GateList.eval, Gate.eval, extendEnv, Size1.Defs0.f_0]⟩

def f_0_lower : ∀ j, j < 1 → ¬HasCircuitOfSize Size1.Defs0.f_0 j := by
  intro j hj
  have : j = 0 := by omega
  subst this
  exact no_size0_of_constant (by simp [Size1.Defs0.f_0])

-- f_1: ¬x₀ — complexity 0

def f_1_size : Nat := 0

def f_1_upper : HasCircuitOfSize Size1.Defs0.f_1 0 :=
  ⟨⟨.nil, ⟨⟨0, by omega⟩, true⟩⟩,
   fun input => by simp [Circuit.eval, Ref.eval, GateList.eval, Size1.Defs0.f_1]⟩

def f_1_lower : ∀ j, j < 0 → ¬HasCircuitOfSize Size1.Defs0.f_1 j :=
  fun _ hj => absurd hj (by omega)

end Size1.Proofs0
