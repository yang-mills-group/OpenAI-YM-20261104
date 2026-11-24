import YM.Integration.FVA1Physical.Sources.AnchorProbability
import YM.Integration.FVA1Physical.Sources.FlaggedFactor

/-! Charge a physical marked insertion on the event that an actual flag
intersects its chosen finite support. -/

namespace YM.PhysicalNext.Repeat.Legato.Bandage.Harmonics

open Filter MeasureTheory Lattice RG Wilson LocalLTE.Sail MergeProof.Accent
open OPE.Therm YM.Integration.FVA1Physical

/-- The probability factor has no dependence on the ambient volume. The other
factor is the finite polynomial in the original inserted-field sup norms. -/
theorem physicalAnchor_testBound {G : Gauge} {H : History G} (hH : H.Selected)
    (hP : Poetry H.levels) (hG : G.Simple) :
    ∀ᶠ i : ℕ in atTop, ∀ (N n : ℕ) (hi : i ≤ N) (A : Support (H.S.side i n))
      (I : Type) [DecidableEq I] [Fintype I] (B : Marker.Census I) (Y : Batch H N n I)
      (u : B.Mode → ℂ), (∀ j, ‖u j‖ ≤ 1) →
      let bad := {v : Config G (H.S.side i n) | ¬ Healthy (H.rep N n i).p.threshold A v}
      ‖(∫ v in bad, modeTest u (gust H N n N (Y.raw B) i hi v) ∂prior G (H.S.side i n)) /
        (Wilson.partition G (H.S.side N n) (H.β N n N) : ℂ)‖ ≤
        terminalInsertionBound Y * (((A.card * 5 ^ 4 * Fintype.card PlaqAxes : ℕ) : ℝ) *
          vanishP H.levels i) := by
  filter_upwards [anchoredFlag_probability hH hP hG] with i hprob
  intro N n hi A I _ _ B Y u hu bad
  have hbad : MeasurableSet bad := (healthy_closed _ A).measurableSet.compl
  have hbound : 0 ≤ terminalInsertionBound Y := by
    unfold terminalInsertionBound
    exact Finset.sum_nonneg fun k _ => mul_nonneg (norm_nonneg _) (pow_nonneg
      (Finset.sum_nonneg fun _ _ => norm_nonneg _) k)
  exact (physicalEvent_testBound B Y hH u hu i hi bad hbad).trans
    (mul_le_mul_of_nonneg_left (hprob N n hi A) hbound)

end YM.PhysicalNext.Repeat.Legato.Bandage.Harmonics
