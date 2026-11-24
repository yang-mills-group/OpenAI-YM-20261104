import YM.Integration.WilsonGraphAppointedWardGroundMatrix
import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7IndependentFiledMaxwellIntegrationByParts
import YM.Maxwell.Reorder
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
noncomputable section

namespace YM.Integration.WilsonGraphAppointedWardUnitFlux

open _root_.YangMills _root_.YangMills.Matching
open _root_.PhysicalMatching.H7StandaloneFourSmearedWardReadings (Pupils)
open _root_.PhysicalMatching.H7StandaloneTranslationTestSupport (weight)
open _root_.PhysicalMatching.H7StandaloneFiledWardMatrixCoefficients (groupMarked fluxEntry rhsCoefficients)
open _root_.PhysicalMatching.H7StandaloneAppointedPublicWardRows (columns unitLabel)
open _root_.PhysicalMatching.H7IndependentFiledMaxwellIntegrationByParts (actualProbes)
open MeasureTheory
open scoped BigOperators Classical ContDiff

variable {g : GaugeGroup} {H : g.core.Simple}
  (Z : _root_.YM.FVA2.Register.WilsonPrescription g.core)
  (Q : _root_.YM.Answer.ContinuumLimit.Perspective H Z true)

theorem directionAt (P : Pupils) (a : Axis) (z : Spacetime × Points 2) :
    weight P a z * groupMarked Z Q 0 a 0 0 (fun _ : Fin 2 => 0) (Ward.prepend z.1 z.2) =
      if a = 0 then weight P a z * _root_.YM.Maxwell.Wick.moment g.core z.2 (actualProbes H) else 0 := by
  by_cases hw : weight P a z = 0
  · simp [hw]
  have hx := _root_.PhysicalMatching.H7StandaloneTranslationTestSupport.separated P a (subset_tsupport _ hw)
  rw [WilsonGraphAppointedWardGroundMatrix.marked Z Q a 0 (fun _ : Fin 2 => 0) _ hx]
  by_cases ha : a = 0
  · subst a
    rw [if_pos rfl]
    unfold WilsonGraphWardGroundMatrix.reading
    rw [_root_.PhysicalMatching.H7IndependentGroupFirstWardTree.groupLeading _ _ _ hx]
    have ht : P.translation z.2 ≠ 0 := by
      intro h
      exact hw (by simp [weight, h])
    have htail : z.2 ∈ _root_.YM.conf 2 := P.translation.tsupport_subset (subset_tsupport _ ht)
    calc
      _ = weight P 0 z * _root_.YM.Maxwell.Wick.moment g.core (_root_.YM.Points.cons z.1 z.2) (Fin.cons 1 (actualProbes H)) := by
        apply congrArg (fun v => weight P 0 z * (maxwellReference g).moment (Ward.prepend z.1 z.2) v)
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · change (if (0 : Axis) = 0 then unitLabel H else 0).val = 1
          simp [unitLabel]
        · rfl
      _ = _ := congrArg (fun v => weight P 0 z * v) (_root_.YM.Maxwell.Wick.adjoin htail z.1 (actualProbes H)).symm
  · rw [if_neg ha]
    have hcol : columns H a 0 0 = 0 := by
      change (if a = 0 then unitLabel H else 0) = 0
      rw [if_neg ha]
    rw [hcol]
    exact mul_eq_zero.mpr (Or.inr (WilsonGraphWardGroundMatrix.zeroReading
      (g := g) (n := 2)
      (_root_.IssuedBridge.PostedAppointedConversion.filed Z Q.MS Q.matching
        (_root_.YM.FVA2.Teller.logNu 1))
      (fun _ : Fin 2 => _root_.PhysicalMatching.H7StandaloneFourSmearedWardReadings.probes H 0)
      (Ward.prepend z.1 z.2) hx))

theorem cutoffIntegral (χ : Spacetime → ℝ) (hs : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (a : Axis) :
    (∫ y : Spacetime, ((fderiv ℝ χ y (EuclideanSpace.single a 1) : ℝ) : ℂ)) = 0 := by
  let e : Spacetime := EuclideanSpace.single a 1
  have hd : Integrable (fun y => fderiv ℝ χ y e) := ((hs.continuous_fderiv (by simp)).clm_apply continuous_const).integrable_of_hasCompactSupport (hc.fderiv_apply ℝ e)
  have h1 : Integrable (fun y => fderiv ℝ χ y e * (1 : ℝ)) := by simpa using hd
  have h2 : Integrable (fun y => χ y * fderiv ℝ (fun _ : Spacetime => (1 : ℝ)) y e) := by simp
  have h3 : Integrable (fun y => χ y * (1 : ℝ)) := by simpa using hs.continuous.integrable_of_hasCompactSupport hc
  have ibp := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable h1 h2 h3 (fun y _ => hs.differentiable (by simp) y) (fun _ _ => differentiableAt_const _)
  have hz : (∫ y, fderiv ℝ χ y e) = 0 := by
    simp [smul_eq_mul] at ibp
    linarith
  change (∫ y, ((fderiv ℝ χ y e : ℝ) : ℂ)) = 0
  simp only [integral_complex_ofReal, hz, Complex.ofReal_zero]

theorem atPupils (P : Pupils) : fluxEntry Z Q P 0 0 = 0 := by
  have h (a : Axis) : (∫ z : Spacetime × Points 2, weight P a z * groupMarked Z Q 0 a 0 0 (fun _ : Fin 2 => 0) (Ward.prepend z.1 z.2)) = 0 := by
    rw [integral_congr_ae (Filter.Eventually.of_forall (directionAt Z Q P a))]
    by_cases ha : a = 0
    · subst a
      change (∫ z : Spacetime × Points 2, weight P 0 z * _root_.YM.Maxwell.Wick.moment g.core z.2 (actualProbes H)) = 0
      by_cases empty : ∀ x : Points 2, P.translation x = 0
      · simp [weight, empty]
      obtain ⟨x, hx⟩ := not_forall.mp empty
      have window := P.window x (subset_tsupport _ hx)
      let f : Spacetime → ℂ := fun y => ((fderiv ℝ P.cutoff y (EuclideanSpace.single (0 : Axis) 1) : ℝ) : ℂ)
      let v : Points 2 → ℂ := fun t => P.translation t * _root_.YM.Maxwell.Wick.moment g.core t (actualProbes H)
      have factored (z : Spacetime × Points 2) : weight P 0 z * _root_.YM.Maxwell.Wick.moment g.core z.2 (actualProbes H) = f z.1 * v z.2 := by
        change (P.translation z.2 * f z.1) * _ = f z.1 * (P.translation z.2 * _)
        ring
      calc
        _ = ∫ z : Spacetime × Points 2, f z.1 * v z.2 := integral_congr_ae (Filter.Eventually.of_forall factored)
        _ = (∫ y, f y) * ∫ t, v t := integral_prod_mul f v
        _ = 0 := by
          have hf : (∫ y, f y) = 0 := cutoffIntegral P.cutoff window.1 window.2.1 0
          rw [hf, zero_mul]
    · simp [ha]
  simp [fluxEntry, h]

end YM.Integration.WilsonGraphAppointedWardUnitFlux
end

