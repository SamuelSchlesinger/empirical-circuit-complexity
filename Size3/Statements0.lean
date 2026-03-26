import Circuits.Basic
import Size3.Defs0
import Size3.Proofs0

/-
  Circuit complexity theorems for 14 representative functions
  of 3 input variable(s) (batch 0).

  Each theorem references proof terms from Size3.Proofs0,
  which must provide for each representative function index idx:
    f_{idx}_size  : Nat
    f_{idx}_upper : Circuits.HasCircuitOfSize Size3.Defs0.f_{idx} f_{idx}_size
    f_{idx}_lower : ∀ j, j < f_{idx}_size →
                      ¬ Circuits.HasCircuitOfSize Size3.Defs0.f_{idx} j
-/

namespace Size3.Statements0

theorem f_0_complexity :
    Circuits.CircuitComplexity Size3.Defs0.f_0 Size3.Proofs0.f_0_size :=
  ⟨Size3.Proofs0.f_0_upper, Size3.Proofs0.f_0_lower⟩

theorem f_1_complexity :
    Circuits.CircuitComplexity Size3.Defs0.f_1 Size3.Proofs0.f_1_size :=
  ⟨Size3.Proofs0.f_1_upper, Size3.Proofs0.f_1_lower⟩

theorem f_3_complexity :
    Circuits.CircuitComplexity Size3.Defs0.f_3 Size3.Proofs0.f_3_size :=
  ⟨Size3.Proofs0.f_3_upper, Size3.Proofs0.f_3_lower⟩

theorem f_6_complexity :
    Circuits.CircuitComplexity Size3.Defs0.f_6 Size3.Proofs0.f_6_size :=
  ⟨Size3.Proofs0.f_6_upper, Size3.Proofs0.f_6_lower⟩

theorem f_7_complexity :
    Circuits.CircuitComplexity Size3.Defs0.f_7 Size3.Proofs0.f_7_size :=
  ⟨Size3.Proofs0.f_7_upper, Size3.Proofs0.f_7_lower⟩

theorem f_15_complexity :
    Circuits.CircuitComplexity Size3.Defs0.f_15 Size3.Proofs0.f_15_size :=
  ⟨Size3.Proofs0.f_15_upper, Size3.Proofs0.f_15_lower⟩

theorem f_22_complexity :
    Circuits.CircuitComplexity Size3.Defs0.f_22 Size3.Proofs0.f_22_size :=
  ⟨Size3.Proofs0.f_22_upper, Size3.Proofs0.f_22_lower⟩

theorem f_23_complexity :
    Circuits.CircuitComplexity Size3.Defs0.f_23 Size3.Proofs0.f_23_size :=
  ⟨Size3.Proofs0.f_23_upper, Size3.Proofs0.f_23_lower⟩

theorem f_24_complexity :
    Circuits.CircuitComplexity Size3.Defs0.f_24 Size3.Proofs0.f_24_size :=
  ⟨Size3.Proofs0.f_24_upper, Size3.Proofs0.f_24_lower⟩

theorem f_25_complexity :
    Circuits.CircuitComplexity Size3.Defs0.f_25 Size3.Proofs0.f_25_size :=
  ⟨Size3.Proofs0.f_25_upper, Size3.Proofs0.f_25_lower⟩

theorem f_27_complexity :
    Circuits.CircuitComplexity Size3.Defs0.f_27 Size3.Proofs0.f_27_size :=
  ⟨Size3.Proofs0.f_27_upper, Size3.Proofs0.f_27_lower⟩

theorem f_30_complexity :
    Circuits.CircuitComplexity Size3.Defs0.f_30 Size3.Proofs0.f_30_size :=
  ⟨Size3.Proofs0.f_30_upper, Size3.Proofs0.f_30_lower⟩

theorem f_60_complexity :
    Circuits.CircuitComplexity Size3.Defs0.f_60 Size3.Proofs0.f_60_size :=
  ⟨Size3.Proofs0.f_60_upper, Size3.Proofs0.f_60_lower⟩

theorem f_105_complexity :
    Circuits.CircuitComplexity Size3.Defs0.f_105 Size3.Proofs0.f_105_size :=
  ⟨Size3.Proofs0.f_105_upper, Size3.Proofs0.f_105_lower⟩

end Size3.Statements0
