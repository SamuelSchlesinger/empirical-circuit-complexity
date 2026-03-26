import Circuits.Basic
import Size2.Defs0
import Size2.Proofs0

/-
  Circuit complexity theorems for 4 representative functions
  of 2 input variable(s) (batch 0).

  Each theorem references proof terms from Size2.Proofs0,
  which must provide for each representative function index idx:
    f_{idx}_size  : Nat
    f_{idx}_upper : Circuits.HasCircuitOfSize Size2.Defs0.f_{idx} f_{idx}_size
    f_{idx}_lower : ∀ j, j < f_{idx}_size →
                      ¬ Circuits.HasCircuitOfSize Size2.Defs0.f_{idx} j
-/

namespace Size2.Statements0

theorem f_0_complexity :
    Circuits.CircuitComplexity Size2.Defs0.f_0 Size2.Proofs0.f_0_size :=
  ⟨Size2.Proofs0.f_0_upper, Size2.Proofs0.f_0_lower⟩

theorem f_1_complexity :
    Circuits.CircuitComplexity Size2.Defs0.f_1 Size2.Proofs0.f_1_size :=
  ⟨Size2.Proofs0.f_1_upper, Size2.Proofs0.f_1_lower⟩

theorem f_3_complexity :
    Circuits.CircuitComplexity Size2.Defs0.f_3 Size2.Proofs0.f_3_size :=
  ⟨Size2.Proofs0.f_3_upper, Size2.Proofs0.f_3_lower⟩

theorem f_6_complexity :
    Circuits.CircuitComplexity Size2.Defs0.f_6 Size2.Proofs0.f_6_size :=
  ⟨Size2.Proofs0.f_6_upper, Size2.Proofs0.f_6_lower⟩

end Size2.Statements0
