import YM.Frontier.Tuning.DominatedHol
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-! Elementary local bounded convergence for scalar holomorphic functions, then real directional jet exchange by bounded slopes on common neighborhoods. No uniform rates required in this local analysis. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier.Tuning.JetHol
open Filter Set MeasureTheory Complex Metric Function Topology ConnectedActivityE6 Blaze
open scoped Topology ContDiff
variable {α : Type*}{F: α→ℂ→ℂ} {G:ℂ→ℂ}{U:Set ℂ}{μ:Filter α}[NeBot μ]
set_option maxHeartbeats 600000 in
lemma bounded_convergence (hU:IsOpen U) (hF:∀ᶠ n in μ,DifferentiableOn ℂ (F n) U) (hG:∀ x∈U,Tendsto (fun n=>F n x) μ (𝓝 (G x)))
   (hp:∀ x∈U,∃ S∈𝓝 x,∃ C:ℝ,∀ᶠ n in μ,∀ z∈ S, ‖F n z‖≤C): TendstoLocallyUniformlyOn F G μ U ∧ DifferentiableOn ℂ G U:=by
  suffices b:TendstoLocallyUniformlyOn F G μ U by exact ⟨b,b.differentiableOn hF hU⟩
  apply Metric.tendstoLocallyUniformlyOn_iff.mpr; intro ε hε x hx
  obtain ⟨W,hw,C,hc⟩:= hp x hx
  obtain ⟨d,hd,hdx⟩:= Metric.mem_nhds_iff.mp (inter_mem hw (hU.mem_nhds hx))
  let r:=d/2; have hr:0<r:=half_pos hd
  let s:=r/2; have hs:0<s:=half_pos hr
  have hV : closedBall x r⊆U:= fun i hi=> (hdx (mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hi) (half_lt_self hd)))).2
  have hdiff : ∀ᶠ n in μ, ∀ v w, v∈closedBall x s→ w∈closedBall x s→dist (F n v) (F n w) ≤ C/s*dist v w:=by
    filter_upwards [hF,hc] with n hF hc v w hv hw
    have hde (t:ℂ)(ht:t∈ closedBall x s) : ‖fderiv ℂ (F n) t‖ ≤ C/s := by
      have hvt y (hy:y∈closedBall t s) : dist y x≤r:= (dist_triangle _ _ _).trans (by unfold s at hy ht; linarith only [mem_closedBall.mp hy,mem_closedBall.mp ht])
      have hh : closure (ball t s)⊆U := fun y hy=> hV (mem_closedBall.mpr (hvt y (closure_ball_subset_closedBall hy)))
      apply (norm_deriv_eq_norm_fderiv).symm.le.trans
      exact norm_deriv_le_of_forall_mem_sphere_norm_le hs ⟨(hF.mono (Subset.trans subset_closure hh)),fun y hy=> (hF.differentiableAt (hU.mem_nhds (hh hy))).continuousAt.continuousWithinAt⟩ (fun y hy=> hc _ (hdx (mem_ball.mpr ((hvt y (sphere_subset_closedBall hy)).trans_lt (half_lt_self hd)))).1)
    have hsub y (hy:y∈closedBall x s):= hF.differentiableAt (hU.mem_nhds (hV (closedBall_subset_closedBall (show s≤r from half_le_self hr.le) hy)))
    simpa [dist_eq_norm_sub] using! (convex_closedBall x s).norm_image_sub_le_of_norm_fderiv_le hsub hde hw hv
  replace hdiff:∀ᶠ n in μ, ∀ v w, v∈closedBall x s→w∈closedBall x s→dist (F n v) (F n w) ≤ (1+|C/s|)*dist v w:=hdiff.mono (fun n hn v w hv hw=>(hn v w hv hw).trans (by gcongr; exact (le_abs_self _).trans (le_add_of_nonneg_left zero_le_one)))
  let D:=1+|C/s|
  have hdif (v w:ℂ)(hv:v∈closedBall x s)(hw:w∈closedBall x s):dist (G v) (G w)≤D*dist v w:= by
    let sub' := hV (closedBall_subset_closedBall (half_le_self hr.le) hv); let sub'' := hV (closedBall_subset_closedBall (half_le_self hr.le) hw)
    exact le_of_tendsto ((hG v sub').dist (hG w sub'')) (by filter_upwards [hdiff] with n hn using hn v w hv hw)
  have ht:0<D:= add_pos_of_pos_of_nonneg zero_lt_one (abs_nonneg _)
  have hδ:0< min s (ε/(3*D)):= lt_min hs (div_pos hε (mul_pos (by norm_num) ht))
  refine ⟨ball x (min s (ε/(3*D))),mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x hδ),?_⟩
  filter_upwards [hdiff,(hG x hx).eventually (ball_mem_nhds _ (by positivity:0<ε/3))] with n hn hy y hy'
  rw [mem_ball] at hy'; have h':y∈closedBall x s:= by have hd:= (lt_min_iff.mp hy').1; exact mem_closedBall.mpr hd.le
  have h0:x∈closedBall x s:= mem_closedBall_self hs.le
  have he' : dist (G y) (F n y) ≤ dist (G y) (G x)+dist (F n x) (G x)+ dist (F n y) (F n x) := by have hd:=dist_triangle (G y) (G x) (F n y); have hd':=dist_triangle (G x) (F n x) (F n y); rw [dist_comm _ (F n x),dist_comm (F n x)] at hd'; linarith [dist_comm (G x) (F n x),dist_comm (F n x) (F n y)]
  apply he'.trans_lt; have hyx : D*dist y x < ε/3 := by
    rw [mul_comm D]; apply (lt_div_iff₀ ht).mp
    calc _ < _ := (lt_min_iff.mp hy').2
         _ = _ := by ring

  linarith only [hn y x h' h0,hdif y x h' h0,mem_ball.mp hy,hyx]

variable {E: Type*}[NormedAddCommGroup E][NormedSpace ℝ E]{g:E→ℂ→ℂ}{J₀:ℕ}
lemma derivative_exchange {S:Set E} {B:ℝ} (hS:IsOpen S)(hU:IsOpen U)
    (hf:∀ y∈S, DifferentiableOn ℂ (g y) U ∧ ∀ z∈U,Brush J₀ B 1 (g · z) y) : ∀ k≤J₀, ∀ y∈S, ∀ m:Fin k→E, DifferentiableOn ℂ (fun z=> iteratedFDeriv ℝ k (g · z) y m) U:=by
 classical
 intro k
 induction k with
 | zero=> intro hk y hy m; exact (hf y hy).1
 | succ k ih=>
   intro hk y hy m
   let J (k:ℕ) (z:ℂ) y:= iteratedFDeriv ℝ k (g · z) y
   have hd z (hz:z∈U) y (hy:y∈S) : DifferentiableAt ℝ (J k z) y := ((hf y hy).2 z hz).smooth.differentiableAt_iteratedFDeriv (by exact_mod_cast (hk:k<J₀))
   let h (t:ℝ):= y+t • m 0
   let q := 𝓝[≠] (0:ℝ)
   let H (t:ℝ) z:= t⁻¹ • ((J k z (h t)-J k z y) (Fin.tail m))
   have hh : Tendsto h q (𝓝 y):= by simpa [h] using! ((show Continuous (fun t:ℝ=>y+t•m 0) from by fun_prop).continuousAt (x:=0) |>.tendsto.mono_left (show q ≤ 𝓝 0 from inf_le_left))
   obtain ⟨r,hr,hrop⟩:= Metric.mem_nhds_iff.mp (hS.mem_nhds hy)
   have hv:=hh.eventually (ball_mem_nhds y hr)
   have h0: y∈ ball y r:= Metric.mem_ball_self hr
   have he: ∀ᶠ t in q,DifferentiableOn ℂ (H t) U:=by
     filter_upwards [hv] with t ht
     exact (ih (Nat.le_of_succ_le hk) (y+ t • m 0) (hrop ht) (Fin.tail m)).sub (ih (Nat.le_of_succ_le hk) y hy (Fin.tail m)) |>.const_smul t⁻¹
   have hB (t:ℝ)(ht:h t∈ball y r)(z:ℂ)(hz:z∈U): ‖H t z‖ ≤ B*‖m 0‖ * ∏ i, ‖Fin.tail m i‖:= by
     have hF x (hx:x∈ball y r) : ‖fderiv ℝ (J k z) x‖ ≤ B:= by rw [norm_fderiv_iteratedFDeriv];simpa [one_pow] using ((hf x (hrop hx)).2 z hz).order _ hk
     have hd':= (convex_ball y r).norm_image_sub_le_of_norm_fderiv_le (fun x hx=>hd z hz x (hrop hx)) hF h0 ht
     rw [show (y+t • m 0)-y=t • m 0 by abel,norm_smul] at hd'
     calc
       _ = ‖(t:ℝ)⁻¹‖ * ‖(J k z (h t)-J k z y) (Fin.tail m)‖ := norm_smul ..
       _ ≤ ‖t⁻¹‖ * ((B*(‖t‖*‖m 0‖))*(∏ i,‖Fin.tail m i‖)) := by gcongr; exact ((J k z (h t)-J k z y).le_opNorm ..).trans (by gcongr <;> try positivity)
       _ = (‖t⁻¹‖*‖t‖) * (B*‖m 0‖ * ∏ i, ‖Fin.tail m i‖) := by rw [norm_inv]; ring
       _ ≤ _ := by
         by_cases htf:t=0
         · subst t; have hvB:=((hf y hy).2 z hz).nonneg; rw [show ‖(0:ℝ)⁻¹‖=0 by simp,zero_mul,zero_mul]; positivity
         · rw [norm_inv,inv_mul_cancel₀ (norm_ne_zero_iff.mpr htf),one_mul]
   have hl z (hz:z∈U): Tendsto (fun t=> H t z) q (𝓝 (J (k+1) z y m)):=by
      
      have hl:=(hd z hz y hy).hasFDerivAt.hasLineDerivAt (m 0) |>.tendsto_slope_zero
      have hh:= (show Continuous (fun p:E [×k]→L[ℝ] ℂ=>p (Fin.tail m)) by fun_prop).continuousAt.tendsto.comp hl
      convert hh using 1
      · funext t; rfl
      · exact congr_arg 𝓝 (iteratedFDeriv_succ_apply_left m)
   exact (bounded_convergence hU he hl (fun z hz=>⟨U,hU.mem_nhds hz,(B*‖m 0‖*∏ i,‖Fin.tail m i‖),hv.mono fun t ht z hz=>hB t ht z hz⟩)).2
end YM.Frontier.Tuning.JetHol
