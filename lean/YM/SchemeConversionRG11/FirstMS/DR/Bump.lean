import YM.MSbar.Dim.MellinLift
import YM.Space.Configurations

/-!
Continuous shells for position DR on the diagnostic. Chose no positivity or monotonicity of
cutoff--it's smooth and constant near the subgraph. We'll need both near and compactified IR.
-/

set_option autoImplicit false
noncomputable section
namespace YM.SchemeConversionRG11.FirstMS.DR
open Function Set Filter MeasureTheory Metric
open scoped Topology ContDiff

def edge : ContDiffBump (0:ℝ) := ⟨1/4,1,by norm_num,by norm_num⟩
abbrev cap (p : ℝ) : ℝ := edge p

def lip (p : ℝ) : ℝ := -(2*p)*deriv cap p

lemma cap_smooth : ContDiff ℝ ∞ cap := edge.contDiff
lemma cap_flat {p:ℝ} (hp : |p| ≤ 1/4) : cap p = 1 :=
  edge.one_of_mem_closedBall (by simpa only [edge,mem_closedBall_iff_norm,sub_zero,Real.norm_eq_abs]) -- target from hp
lemma cap_ends {p:ℝ} (hp : 1 ≤ p) : cap p = 0 := edge.zero_of_le_dist (by
  simpa only [edge, dist_zero_right,Real.norm_eq_abs] using hp.trans (le_abs_self _))
lemma lip_smooth : ContDiff ℝ ∞ lip := (contDiff_const.mul contDiff_id |>.neg).mul
   (contDiff_infty_iff_deriv.mp cap_smooth).2
lemma lip_packed {p : ℝ} (hp : ¬ p ∈ closedBall (0:ℝ) 1) : lip p = 0 := by
  have hs : p ∉ tsupport cap := by rw [show tsupport cap = _ from edge.tsupport_eq]; exact hp
  unfold lip
  rw [(notMem_tsupport_iff_eventuallyEq.mp hs).deriv_eq]; simp
lemma lip_ends {p:ℝ} (h : 1 < p) : lip p = 0 := lip_packed (by
  simp only [mem_closedBall,dist_zero_right,Real.norm_eq_abs,not_le]
  exact h.trans_le (le_abs_self _))
lemma lip_flats {p : ℝ} (hp : |p| < 1/4) : lip p = 0 := by
  have he : cap =ᶠ[𝓝 p] fun _ ↦ 1 := edge.eventuallyEq_one_of_mem_ball
    (by simpa only [edge, mem_ball,dist_zero_right,Real.norm_eq_abs] using hp)
  rw [lip,he.deriv_eq]; simp

lemma scale_has (p t : ℝ) (h : t ≠ 0) : HasDerivAt (fun t : ℝ ↦ cap (p/t^2)) (lip (p/t^2)/t) t := by
  refine ((cap_smooth.differentiable (by simp) _).hasDerivAt.comp t ((hasDerivAt_const _ p).div ((hasDerivAt_id' t).pow 2) (pow_ne_zero _ h))).congr_deriv ?_
  unfold lip; simp only [Pi.div_apply, Pi.pow_apply]; field_simp; ring
lemma dest_has (p t : ℝ) (_h : t ≠ 0) : HasDerivAt (fun t : ℝ ↦ cap (p*t^2)) (-(lip (p*t^2)/t)) t := by
  refine ((cap_smooth.differentiable (by simp) _).hasDerivAt.comp t (((hasDerivAt_id' t).pow 2).const_mul p)).congr_deriv ?_
  unfold lip; simp only [Pi.pow_apply]; field_simp [_h]; ring

variable {p R : ℝ} (hR : 0 < R) (hp : 0 < p)

/-- Continuous near shell. Singular else-definition at t=0 harmless. -/
lemma scale_cost (hp : 0 < p) : Continuous (fun t : ℝ ↦ lip (p/t^2)/t) := by
  rw [continuous_iff_continuousAt]; intro t
  rcases eq_or_ne t 0 with rfl|h
  · apply (continuousAt_const (y:= (0:ℝ))).congr
    have he : ∀ᶠ t : ℝ in 𝓝 0,t^2 < p := by
      exact ((show Continuous (fun t : ℝ ↦ t^2) from continuous_id.pow 2).continuousAt (x:=0)|>.tendsto).eventually (gt_mem_nhds (show (0:ℝ)^2<p by simpa))
    filter_upwards [he] with t ht
    by_cases hh : t = 0; rw [hh]; simp
    rw [lip_ends ((lt_div_iff₀ (sq_pos_of_ne_zero hh)).2 (by simpa)),zero_div]
  exact (lip_smooth.continuous.continuousAt.comp (continuousAt_const.div (continuousAt_id.pow 2) (pow_ne_zero _ h))).div continuousAt_id h
lemma dest_cost (p : ℝ) : Continuous (fun t : ℝ ↦ lip (p*t^2)/t) := by
  rw [continuous_iff_continuousAt]; intro t
  rcases eq_or_ne t 0 with rfl|h
  · apply (continuousAt_const (y:= (0:ℝ))).congr
    have he : ∀ᶠ t : ℝ in 𝓝 0, |p*t^2| < 1/4 := by
      exact ((show Continuous (fun t : ℝ ↦ |p*t^2|) by fun_prop).continuousAt (x:=0) |>.tendsto).eventually (gt_mem_nhds (show |p*(0:ℝ)^2| < 1/4 by norm_num))
    filter_upwards [he] with t ht; rw [lip_flats ht,zero_div]
  exact (lip_smooth.continuous.continuousAt.comp (continuousAt_const.mul (continuousAt_id.pow 2))).div continuousAt_id h

lemma scale_volume (hR : 0 < R) (hp : 0 < p) : (∫ t in Ioc 0 R, lip (p/t^2)/t) = cap (p/R^2) := by
   classical
   let f (t : ℝ) := if t=0 then 0 else cap (p/t^2)
   have hE (t : ℝ) (ht : t≠0) : f =ᶠ[𝓝 t] fun t ↦ cap (p/t^2) := by
      filter_upwards [eventually_ne_nhds ht] with v hv; unfold f; rw [if_neg hv]
   have hh (t : ℝ) (ht : t≠0) : HasDerivAt f (lip (p/t^2)/t) t := (scale_has p t ht).congr_of_eventuallyEq (hE t ht)
   have he : Continuous f := by
      rw [continuous_iff_continuousAt]; intro t; rcases eq_or_ne t 0 with rfl|hr
      · refine (continuousAt_const (y:=(0:ℝ))).congr ?_
        let K (t : ℝ) := t^2
        have hk : Continuous K := continuous_id.pow _
        have hw : ∀ᶠ t : ℝ in 𝓝 0,K t < p := hk.continuousAt.tendsto.eventually (gt_mem_nhds (by simp [K,hp]))
        filter_upwards [hw] with t ht; rcases eq_or_ne t 0 with rfl|hv
        · exact (if_pos rfl : f 0 = 0).symm
        rw [(hE t hv).eq_of_nhds]; exact (cap_ends ((one_le_div (sq_pos_of_ne_zero hv)).mpr ht.le)).symm
      exact (hh t hr).continuousAt
   rw [← intervalIntegral.integral_of_le hR.le, intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hR.le he.continuousOn (fun t ht=>hh t ht.1.ne') ((scale_cost hp).intervalIntegrable ..),(hE _ hR.ne').eq_of_nhds, show f 0=0 from if_pos rfl,sub_zero]
lemma dest_volume (p : ℝ) (hR : 0 < R) : (∫ t in Ioc 0 R, lip (p*t^2)/t) = 1-cap (p*R^2) := by
   let f (t : ℝ) := -cap (p*t^2)
   have he : Continuous f := (cap_smooth.continuous.comp (continuous_id.pow _|>.const_mul p)).neg
   rw [← intervalIntegral.integral_of_le hR.le, intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hR.le he.continuousOn (fun t ht=>show HasDerivAt f _ _ from by simpa using! (dest_has p t ht.1.ne').neg) ((dest_cost p).intervalIntegrable ..)]
   simp [f, cap_flat (p:=0) (by norm_num),sub_eq_add_neg,add_comm]

end YM.SchemeConversionRG11.FirstMS.DR
