import YM.Integration.WilsonLimitConstruction.LocalHolomorphicRay
import YM.Integration.WilsonLimitConstruction.FundedWilsonAtlas
import Mathlib.Analysis.Complex.RealDeriv

/-! One common holomorphic disk for the entire finite product Haar prior
and the physically regularized Wilson action. Its radius is chosen before
every period, lattice, normalized link field and analytic correction. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedWilsonJointDisk

open Function Filter Finset Set Metric Lattice Wilson RG Exterior PertExtension
open FundedWilsonGerm FundedWilsonAtlas
open scoped Topology ContDiff NNReal ENNReal BigOperators
variable {G : Gauge} {n : Side}

theorem divided (S : FundedWilsonPlaquette.Sheet G) (B : fieldDir G n 1)
    (hB : ∀ i, ‖directions B i‖ ≤ 1) :
    ∃ Q : ℂ → ℂ, AnalyticOnNhd ℂ Q (Metric.eball 0 S.radius) ∧
      ∀ z : ℂ, complexEnergy S B z = z^2 * Q z := by
  let E := complexEnergy S B
  have hr : (0:ℝ) < S.radius := S.radius_pos
  have h0 : (0:ℂ) ∈ Metric.eball 0 S.radius := by simpa using hr
  have hE := holomorphic S B hB
  have hE₀ : AnalyticAt ℂ E 0 := hE _ h0
  have hz : E 0 = 0 := by
    simpa only [Complex.ofReal_zero,zero] using (real_axis S B hB (t := 0) (by simpa using hr))
  have href : (fun t : ℝ => E (t:ℂ)) =ᶠ[𝓝 0] (fun t => (action B t : ℂ)) := by
    filter_upwards [Metric.ball_mem_nhds (0:ℝ) hr] with t ht
    exact real_axis S B hB (mem_ball_zero_iff.mp ht)
  have hc : HasDerivAt (fun t : ℝ => E (t:ℂ)) (deriv E 0) 0 :=
    hE₀.differentiableAt.hasDerivAt.comp_ofReal
  have ha : HasDerivAt (fun t : ℝ => (action B t:ℂ)) 0 0 := by
    simpa only [slope,Complex.ofReal_zero] using
      (FundedWilsonGerm.analytic B).differentiableAt.hasDerivAt.ofReal_comp
  have hd : deriv E 0 = 0 := hc.unique (ha.congr_of_eventuallyEq href)
  obtain ⟨Q,hQ,hf⟩ := hE₀.exists_eq_sum_add_pow_mul 2
  have hfactor (z : ℂ) : E z = z^2 * Q z := by
    simpa [Finset.sum_range_succ,hz,hd,smul_eq_mul] using hf z
  refine ⟨Q,fun z hmem => ?_,hfactor⟩
  by_cases hzero : z = 0
  · subst z; exact hQ
  have hanalytic : AnalyticAt ℂ (fun w : ℂ => E w / w^2) z :=
    (hE z hmem).div (analyticAt_id.pow 2) (pow_ne_zero _ hzero)
  apply hanalytic.congr
  filter_upwards [eventually_ne_nhds hzero] with w hw
  rw [hfactor w]
  field_simp

def prior (S : LocalHolomorphicRay.Sheet (Chart.fee (XSpace.Bare.chart G)))
    (B : fieldDir G n 1) (z : ℂ) :=
  ∏ e : Edge (Site n), (LocalHolomorphicRay.complexSeries S (collect G B e)).sum z

theorem prior_axis (S : LocalHolomorphicRay.Sheet (Chart.fee (XSpace.Bare.chart G)))
    (B : fieldDir G n 1) (hB : ∀ e, ‖collect G B e‖ ≤ 1) {t : ℝ}
    (ht : ‖t‖ < (S.radius:ℝ)) : prior S B (t:ℂ) = FundedWilsonMeasure.priorWeight B t := by
  unfold prior FundedWilsonMeasure.priorWeight Chart.jacobian
  push_cast
  exact Finset.prod_congr rfl fun e _ => LocalHolomorphicRay.real_axis S (hB e) ht

theorem prior_holomorphic (S : LocalHolomorphicRay.Sheet (Chart.fee (XSpace.Bare.chart G)))
    (B : fieldDir G n 1) (hB : ∀ e, ‖collect G B e‖ ≤ 1) :
    AnalyticOnNhd ℂ (prior S B) (Metric.eball 0 S.radius) := by
  intro z hz
  exact Finset.analyticAt_fun_prod _ fun e _ =>
    (LocalHolomorphicRay.complex_disc S (hB e)).analyticAt_of_mem hz

theorem purchase (G : Gauge) : ∃ r : ℝ≥0, 0 < r ∧
    ∀ (n : Side) (B : fieldDir G n 1), (∀ e, ‖collect G B e‖ ≤ 1) →
    ∀ (P : ℝ → ℝ) (p : ℂ → ℂ), AnalyticOnNhd ℂ p (Metric.eball 0 r) →
      (∀ t : ℝ, ‖t‖ < r → p (t:ℂ) = (P t:ℂ)) →
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F (Metric.eball 0 r) ∧
      ∀ (C : Curve B) (t : ℝ), t ≠ 0 → ‖t‖ < r →
        F (t:ℂ) = (FundedWilsonMeasure.density C P t : ℂ) := by
  obtain ⟨S⟩ := FundedWilsonPlaquette.purchase G
  obtain ⟨H⟩ := LocalHolomorphicRay.prior G
  let r := min S.radius H.radius
  refine ⟨r,lt_min S.radius_pos H.radius_pos,fun n B hB P p hp realP => ?_⟩
  have hS (i) : ‖directions B i‖ ≤ 1 :=
    (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun a => hB _
  have sS : r ≤ S.radius := min_le_left ..
  have sH : r ≤ H.radius := min_le_right ..
  have hs : Metric.eball (0:ℂ) r ⊆ Metric.eball 0 S.radius :=
    Metric.eball_subset_eball (ENNReal.coe_le_coe.mpr sS)
  have hh : Metric.eball (0:ℂ) r ⊆ Metric.eball 0 H.radius :=
    Metric.eball_subset_eball (ENNReal.coe_le_coe.mpr sH)
  obtain ⟨Q,hQ,hfactor⟩ := divided S B hS
  let F (z : ℂ) := prior H B z * Complex.exp (-(Q z + p z * complexEnergy S B z))
  refine ⟨F,fun z hz => ?_,fun C t ht htr => ?_⟩
  · exact (prior_holomorphic H B hB z (hh hz)).fun_mul
      (((hQ z (hs hz)).fun_add ((hp z hz).fun_mul (holomorphic S B hS z (hs hz)))).neg.cexp)
  · have htS : ‖t‖ < (S.radius:ℝ) := htr.trans_le sS
    have htH : ‖t‖ < (H.radius:ℝ) := htr.trans_le sH
    have hU : Q (t:ℂ) = C.value t := by
      apply mul_left_cancel₀ (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr ht))
      rw [←hfactor,real_axis S B hS htS,C.factor t]
      push_cast
      rfl
    unfold F FundedWilsonMeasure.density FundedWilsonMeasure.gas FundedWilsonGerm.corrected
    rw [prior_axis H B hB htH,hU,realP t htr,real_axis S B hS htS]
    push_cast
    rfl

end YM.Integration.WilsonLimitConstruction.FundedWilsonJointDisk
end
