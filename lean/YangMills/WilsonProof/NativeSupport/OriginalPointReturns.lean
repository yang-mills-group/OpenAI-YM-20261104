import YangMills.WilsonProof.NativeSupport.WilsonConstruction

import YangMills.FiniteVolume
import YangMills.VolumeLimit
import YangMills.StressTensor
import YangMills.WilsonProof.NativeSupport.YangMills.CorrelationHierarchy

/-! The fixed-period kernels obtained from the original Wilson moments. -/

set_option autoImplicit false

noncomputable section

namespace YangMills.Wilson

open Filter MeasureTheory Set

open scoped Topology

variable {g : GaugeGroup}

def Construction.originalPointReturns (run : Construction g) : Prop :=
  ∃ F : PeriodPointTable run.family, FixedPointReturns run.family F ∧
    ∀ (p : ℕ → ℕ) (hp : StrictMono p) (n : ℕ) (v : Fin n → run.family.Token)
        (K : Set (Points n)), IsCompact K → K ⊆ WilsonFamily.separated n →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, ∀ z ∈ K,
        dist (periodValue F (p ((run.refine p hp).indices k)) v z)
          ((run.refine p hp).hierarchy.correlation none
            ((run.refine p hp).hierarchy.project ∘ v) z) < ε

end YangMills.Wilson
