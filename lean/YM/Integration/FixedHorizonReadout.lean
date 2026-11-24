import YM.OPE.Detector
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Normed.Operator.Asymptotics

/-!
Finite separated physical probes determine the original field at one fixed
output horizon. The decoder is the existing `OPE.Detector.report`; its norm
is a fixed finite cost. No scale-dependent inverse estimate is assumed.
Changing to a running field frame exposes its inverse norm explicitly.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Integration.FixedHorizonReadout

open Function Filter OPE
open scoped Topology Classical

variable {G : Gauge} {L : Register G} {S : Table L} {h : ℕ}
    (U : OPE.Detector S h)

def samples : S.Field h →ₗ[ℂ] (Fin U.size → ℂ) :=
  LinearMap.pi fun i => witnessAt S h (U.listen i)

def reportCLM : (Fin U.size → ℂ) →L[ℂ] S.Field h :=
  LinearMap.toContinuousLinearMap U.report

@[simp] theorem report_samples (x : S.Field h) :
    reportCLM U (samples U x) = x := U.recovered x

theorem samples_injective : Injective (samples U) :=
  (show LeftInverse (reportCLM U) (samples U) from report_samples U).injective

theorem report_error_bound (z : Fin U.size → ℂ) (x : S.Field h) :
    ‖reportCLM U z - x‖ ≤ ‖reportCLM U‖ * ‖z - samples U x‖ := by
  have he : reportCLM U z - x = reportCLM U (z - samples U x) := by
    rw [map_sub, report_samples]
  rw [he]
  exact (reportCLM U).le_opNorm _

/-- One constant before all field pairs and all finite probe errors. -/
theorem field_error_bound (ε : ℝ) (hε : 0 ≤ ε) (x y : S.Field h)
    (he : ∀ i, ‖witnessAt S h (U.listen i) x -
      witnessAt S h (U.listen i) y‖ ≤ ε) :
    ‖x - y‖ ≤ ‖reportCLM U‖ * ε := by
  have hs : ‖samples U x - samples U y‖ ≤ ε :=
    (pi_norm_le_iff_of_nonneg hε).mpr he
  simpa only [report_samples] using
    (report_error_bound U (samples U x) y).trans
      (mul_le_mul_of_nonneg_left hs (reportCLM U).opNorm_nonneg)

theorem field_unique (x y : S.Field h)
    (he : ∀ i, witnessAt S h (U.listen i) x =
      witnessAt S h (U.listen i) y) : x = y := by
  apply samples_injective U
  exact funext he

variable {α : Type*} {l : Filter α}

/-- All scalar probe limits at this finite horizon recover the field limit. -/
theorem tendsto_of_samples (f : α → S.Field h) (x : S.Field h)
    (he : ∀ i, Tendsto (fun a => witnessAt S h (U.listen i) (f a)) l
      (𝓝 (witnessAt S h (U.listen i) x))) : Tendsto f l (𝓝 x) := by
  have hs : Tendsto (fun a => samples U (f a)) l (𝓝 (samples U x)) :=
    tendsto_pi_nhds.mpr he
  have ht := (reportCLM U).continuous.continuousAt.tendsto.comp hs
  simpa only [Function.comp_def, report_samples] using ht

/-- Finite scalar remainder bounds transfer without losing their order. -/
theorem isBigO_of_samples {E : Type*} [SeminormedAddCommGroup E]
    (f : α → S.Field h) (g : α → E)
    (he : ∀ i, (fun a => witnessAt S h (U.listen i) (f a)) =O[l] g) :
    f =O[l] g := by
  have hs : (fun a => samples U (f a)) =O[l] g :=
    Asymptotics.isBigO_pi.mpr he
  have ht := ((reportCLM U).isBigO_comp (fun a => samples U (f a)) l).trans hs
  simpa only [report_samples] using ht

theorem isLittleO_of_samples {E : Type*} [SeminormedAddCommGroup E]
    (f : α → S.Field h) (g : α → E)
    (he : ∀ i, (fun a => witnessAt S h (U.listen i) (f a)) =o[l] g) :
    f =o[l] g := by
  have hs : (fun a => samples U (f a)) =o[l] g :=
    Asymptotics.isLittleO_pi.mpr he
  have ht := ((reportCLM U).isBigO_comp
    (fun a => samples U (f a)) l).trans_isLittleO hs
  simpa only [report_samples] using ht

/-- This is the explicit cost if the original fields are expressed in a
running frame. Uniform control of this inverse norm is a separate question. -/
theorem frame_error_bound {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (e : V ≃ₗ[ℂ] S.Field h) (ε : ℝ) (hε : 0 ≤ ε) (x y : V)
    (he : ∀ i, ‖witnessAt S h (U.listen i) (e x) -
      witnessAt S h (U.listen i) (e y)‖ ≤ ε) :
    ‖x - y‖ ≤ ‖LinearMap.toContinuousLinearMap e.symm.toLinearMap‖ *
      ‖reportCLM U‖ * ε := by
  let q := LinearMap.toContinuousLinearMap e.symm.toLinearMap
  have hq : q (e x - e y) = x - y := by
    change e.symm (e x - e y) = x - y
    simp only [map_sub, LinearEquiv.symm_apply_apply]
  rw [← hq]
  exact (q.le_opNorm _).trans
    ((mul_le_mul_of_nonneg_left (field_error_bound U ε hε (e x) (e y) he)
      q.opNorm_nonneg).trans_eq (mul_assoc _ _ _).symm)

/-- The probes and their exact inverse are produced by the same physical
hierarchy; there is no free matrix-invertibility premise. -/
def actualDetector (hs : S.Hierarchy) (h : ℕ) : OPE.Detector S h :=
  (OPE.has_detectors hs h).some

theorem actual_detector_bound (hs : S.Hierarchy) (h : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (ε : ℝ), 0 ≤ ε → ∀ x y : S.Field h,
      (∀ i, ‖witnessAt S h ((actualDetector hs h).listen i) x -
        witnessAt S h ((actualDetector hs h).listen i) y‖ ≤ ε) →
      ‖x - y‖ ≤ K * ε := by
  refine ⟨1 + ‖reportCLM (actualDetector hs h)‖, by positivity, ?_⟩
  intro ε hε x y he
  exact (field_error_bound (actualDetector hs h) ε hε x y he).trans
    (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) hε)

end YM.Integration.FixedHorizonReadout
