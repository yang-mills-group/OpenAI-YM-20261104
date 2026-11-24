import YM.Integration.WilsonLimitConstruction.FundedWilsonSupportGerm
import Mathlib.Analysis.Complex.Liouville

/-! Cauchy estimates on the actual links and plaquettes used by any
finite sector of the Wilson density in the exponential chart. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedWilsonCauchy

open Filter Finset Set Metric Lattice Exterior
open FundedWilsonAtlas
open scoped Topology ContDiff NNReal ENNReal BigOperators
variable {G : Gauge} {n : Side}

theorem half_disk {s : FormalMultilinearSeries ℂ ℂ ℂ} {r : ℝ≥0} {C : ℝ}
    (hr : 0 < r) (h : HasFPowerSeriesOnBall s.sum s 0 r)
    (hb : ∀ k : ℕ, ‖s k‖*(r:ℝ)^k ≤ C) {z : ℂ} (hz : ‖z‖ ≤ (r:ℝ)/2) :
    ‖s.sum z‖ ≤ 2*C := by
  let q : ℝ := 1/2
  have hq : 0 ≤ q := by norm_num [q]
  have hqz : ‖z‖ ≤ q*(r:ℝ) := by simpa [q,div_eq_mul_inv,mul_comm] using hz
  have hterm (k : ℕ) : ‖s k (fun _ => z)‖ ≤ C*q^k := by
    calc
      _ ≤ ‖s k‖ * ‖z‖^k := by simpa using (s k).le_opNorm (fun _ => z)
      _ ≤ ‖s k‖ * (q*(r:ℝ))^k := by gcongr
      _ = (‖s k‖*(r:ℝ)^k)*q^k := by rw [mul_pow]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hb _) (pow_nonneg hq _)
  have hs := h.hasSum (y := z)
    (by simpa only [Metric.eball_coe,Metric.mem_ball,dist_zero_right] using
      hz.trans_lt (half_lt_self (show 0 < (r:ℝ) from hr)))
  have ht := norm_sub_le_of_geometric_bound_of_hasSum (show q<1 by norm_num [q]) hterm hs 0
  norm_num [q] at ht
  linarith

def prior (H : LocalHolomorphicRay.Sheet (PertExtension.Chart.fee (XSpace.Bare.chart G)))
    (B : fieldDir G n 1) (I : Finset (Edge (Site n))) (z : ℂ) :=
  ∏ e ∈ I, (LocalHolomorphicRay.complexSeries H (collect G B e)).sum z

def chartPrior (B : fieldDir G n 1) (I : Finset (Edge (Site n))) (t : ℝ) :=
  ∏ e ∈ I, PertExtension.Chart.fee (XSpace.Bare.chart G) (t • collect G B e)

theorem purchase (G : Gauge) : ∃ ρ MH MW : ℝ, 0 < ρ ∧ 0 < MH ∧ 0 < MW ∧
    ∀ (n : Side) (B : fieldDir G n 1) (I : Finset (Edge (Site n)))
      (J : Finset (MS.Native.Chart.Rout (Site n))),
      (∀ e ∈ I, ‖collect G B e‖ ≤ 1) → (∀ i ∈ J, ‖directions B i‖ ≤ 1) →
    ∀ (p : ℂ → ℂ), AnalyticOnNhd ℂ p (Metric.closedBall 0 ρ) →
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F (Metric.closedBall 0 ρ) ∧
      (∀ (t : ℝ), t ≠ 0 → ‖t‖ ≤ ρ → F (t:ℂ) = (chartPrior B I t : ℝ) *
        Complex.exp (-((FundedWilsonSupportGerm.physical B J t / t^2 : ℝ) +
          p (t:ℂ)*(FundedWilsonSupportGerm.physical B J t:ℝ)))) ∧
      ∀ (A : ℝ), 0 ≤ A → (∀ z ∈ Metric.sphere (0:ℂ) ρ, ‖p z‖ ≤ A) →
      ∀ k : ℕ, ‖iteratedDeriv k F 0‖ ≤ k.factorial *
        (MH^I.card * Real.exp ((J.card:ℝ)*MW*((ρ^2)⁻¹+A))) / ρ^k := by
  obtain ⟨S⟩ := FundedWilsonPlaquette.purchase G
  obtain ⟨H⟩ := LocalHolomorphicRay.prior G
  have hlocal := H.positive
  have hface := S.positive
  let ρ : ℝ := min (S.radius:ℝ) H.radius / 2
  have hρ : 0 < ρ := half_pos (lt_min S.radius_pos H.radius_pos)
  have hS : ρ ≤ (S.radius:ℝ)/2 := by dsimp [ρ]; gcongr; exact min_le_left .. 
  have hH : ρ ≤ (H.radius:ℝ)/2 := by dsimp [ρ]; gcongr; exact min_le_right ..
  have hρS := hS.trans_lt (half_lt_self (show 0 < (S.radius:ℝ) from S.radius_pos))
  have hρH := hH.trans_lt (half_lt_self (show 0 < (H.radius:ℝ) from H.radius_pos))
  refine ⟨ρ,2*H.constant,2*S.constant,hρ,by positivity,by positivity,
    fun n B I J hi hj p hp => ?_⟩
  let E := FundedWilsonSupportGerm.energy S B J
  obtain ⟨Q,hQ,hfactor,haxis⟩ := FundedWilsonSupportGerm.divided S B J hj
  let F (z : ℂ) := prior H B I z * Complex.exp (-(Q z + p z * E z))
  have hF : AnalyticOnNhd ℂ F (Metric.closedBall 0 ρ) := by
    intro z hz
    have hnorm : ‖z‖ ≤ ρ := mem_closedBall_zero_iff.mp hz
    have hs : z ∈ Metric.eball (0:ℂ) S.radius := by simpa using hnorm.trans_lt hρS
    have hh : z ∈ Metric.eball (0:ℂ) H.radius := by simpa using hnorm.trans_lt hρH
    have hprior : AnalyticAt ℂ (prior H B I) z := Finset.analyticAt_fun_prod _ fun e he =>
      (LocalHolomorphicRay.complex_disc H (hi e he)).analyticAt_of_mem hh
    exact hprior.fun_mul (((hQ z hs).fun_add
      ((hp z hz).fun_mul (FundedWilsonSupportGerm.holomorphic S B J hj z hs))).neg.cexp)
  refine ⟨F,hF,fun t ht htρ => ?_,fun A hA ha k => ?_⟩
  · have hprior : prior H B I (t:ℂ) = (chartPrior B I t : ℂ) := by
      unfold prior chartPrior
      push_cast
      exact Finset.prod_congr rfl fun e he =>
        LocalHolomorphicRay.real_axis H (hi e he) (htρ.trans_lt hρH)
    dsimp only [F,E]
    rw [hprior,haxis t ht (htρ.trans_lt hρS),
      FundedWilsonSupportGerm.axis S B J hj (htρ.trans_lt hρS)]
  · apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hρ
      ⟨hF.differentiableOn.mono ball_subset_closedBall,
        hF.continuousOn.mono Metric.closure_ball_subset_closedBall⟩
    intro z hz
    have hrz : ‖z‖ = ρ := by simpa [mem_sphere] using hz
    have hprior : ‖prior H B I z‖ ≤ (2*H.constant)^I.card := by
      unfold prior
      rw [norm_prod]
      calc
        _ ≤ ∏ e ∈ I, (2*H.constant) := by
          apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
          intro e he
          apply half_disk H.radius_pos (LocalHolomorphicRay.complex_disc H (hi e he))
            (fun d => ?_) (hrz.le.trans hH)
          simpa [LocalHolomorphicRay.complexSeries,FormalMultilinearSeries.ofScalars_norm] using
            LocalHolomorphicRay.coefficient_bound H (hi e he) d
        _ = _ := by simp
    let D := (J.card:ℝ)*(2*S.constant)
    have henergy : ‖E z‖ ≤ D := by
      apply (norm_sum_le _ _).trans
      calc
        _ ≤ ∑ i ∈ J, (2*S.constant) := by
          apply Finset.sum_le_sum
          intro i hi
          apply half_disk S.radius_pos (FundedWilsonPlaquette.complex_disc S (hj i hi))
            (fun d => ?_) (hrz.le.trans hS)
          simpa [FundedWilsonPlaquette.complexSeries,FormalMultilinearSeries.ofScalars_norm] using
            FundedWilsonPlaquette.coefficient_bound S (hj i hi) d
        _ = D := by simp [D,nsmul_eq_mul]
    have hq : ‖Q z‖ ≤ D*(ρ^2)⁻¹ := by
      rw [←div_eq_mul_inv]
      apply (le_div_iff₀ (pow_pos hρ 2)).mpr
      calc
        _ = ‖E z‖ := by rw [show E z = _ from hfactor z,norm_mul,norm_pow,hrz,mul_comm]
        _ ≤ D := henergy
    have hcost : ‖-(Q z+p z*E z)‖ ≤ D*((ρ^2)⁻¹+A) := by
      rw [norm_neg]
      calc
        _ ≤ ‖Q z‖ + ‖p z‖*‖E z‖ := by simpa [norm_mul] using norm_add_le (Q z) (p z*E z)
        _ ≤ D*(ρ^2)⁻¹ + A*D := by gcongr; exact ha z hz
        _ = _ := by ring
    dsimp only [F]
    rw [norm_mul,Complex.norm_exp]
    exact mul_le_mul hprior (Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans hcost))
      (Real.exp_pos _).le (pow_nonneg (by positivity) _)

end YM.Integration.WilsonLimitConstruction.FundedWilsonCauchy
end
