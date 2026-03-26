import Circuits.Basic
import Size1.Defs0
import Size1.Proofs0

/-
  Circuit complexity theorems for 2 representative functions
  of 1 input variable(s) (batch 0).

  Each theorem references proof terms from Size1.Proofs0,
  which must provide for each representative function index idx:
    f_{idx}_size  : Nat
    f_{idx}_upper : Circuits.HasCircuitOfSize Size1.Defs0.f_{idx} f_{idx}_size
    f_{idx}_lower : ∀ j, j < f_{idx}_size →
                      ¬ Circuits.HasCircuitOfSize Size1.Defs0.f_{idx} j
-/

namespace Size1.Statements0

theorem f_0_complexity :
    Circuits.CircuitComplexity Size1.Defs0.f_0 Size1.Proofs0.f_0_size :=
  ⟨Size1.Proofs0.f_0_upper, Size1.Proofs0.f_0_lower⟩

theorem f_1_complexity :
    Circuits.CircuitComplexity Size1.Defs0.f_1 Size1.Proofs0.f_1_size :=
  ⟨Size1.Proofs0.f_1_upper, Size1.Proofs0.f_1_lower⟩

end Size1.Statements0
