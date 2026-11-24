import YM.FVA2.O.Lives.Resp
import YM.MS.JetBound
/-!
# Parametric scaled marks: Jet continuities

Velocity is specified only at each assignment, but with Warm (no assumptions
on scale derivatives of those costs), all *momentum* derivatives inherit velocity. This is used
for unconditional Taylor extraction in continuum units. First, continuity of
all jets in a finite-dimensional chart. We do not use inner-region estimates on absolute sizes
of any evolving scale-error differential.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Tune
open MS Function Filter Set Finset MS.Latch Job MS.Plane MeasureTheory Real Metric
open scoped Topology ContDiff
variable {E F I:Type}[NormedAddCommGroup E][NormedSpace ℝ E] [NormedAddCommGroup F][NormedSpace ℝ F]
variable {f H:ℝ→ E→F}{s p:ℝ}
structure Gym (f:ℝ→ E→F) : Prop where
   basic r(h:0≤r): Bound ( single (camp r)) ( slice r f ) 1
lemma Gym.fits (hp:Gym f): Gym (fun i=> fderiv ℝ (f i)) := ⟨fun r h=>by
   simpa only [ slice, cw, mul_one ] using! ( hp.basic r h ).fderiv ⟩
lemma Gym.sm (hp:Gym f)(t:ℝ): ContDiff ℝ ∞ (f t) := (hp.basic _ (by positivity)).smooth (⟨ (),t,existsC t⟩:camp (‖t‖+1))
lemma Gym.day (hp:Gym f) (r s:ℝ)(hr:0≤r)(hs:0≤s) (x:E)(j:ℕ): ∃ K:ℝ,0<K∧∀t∈Set.Icc (-r) r,∀y∈closedBall x s, ‖iteratedFDeriv ℝ j (f t) y‖≤K:= by
    obtain ⟨C,hC,b,hb⟩:= (hp.basic r hr).quoted j; refine ⟨ C*(1+(s+‖x‖))^b,by positivity, fun t ht p hp=>?_⟩; specialize hb (⟨ (),t,ht ⟩:camp r) p trivial; simp only [tx,cw,Pi.one_apply,one_pow,mul_one] at hb; apply le_trans hb; gcongr; exact ( show ‖p‖ ≤ ‖p-x‖+‖x‖ by simpa only [ sub_add_cancel ] using norm_add_le (p-x) x ).trans (add_le_add (mem_closedBall_iff_norm.mp hp) le_rfl )
lemma Gym.slope (hp:Gym f) (r:ℝ)(hr:0≤r)(x v:E): ∃ K:ℝ,0<K∧∀t∈Set.Icc (-r) r,∀ z:ℝ,0<z→z≤1→ dist ( fderiv ℝ (f t) x v ) (z⁻¹ • (f t (x+z • v) - f t x )) ≤ K*z := by
    obtain ⟨K,hK,h⟩:= hp.fits.day r ‖v‖ hr (norm_nonneg _) x 1; simp_rw [norm_iteratedFDeriv_one] at h
    refine ⟨ K*‖v‖^2+1,by positivity, fun t ht z hz hy=>?_⟩; let g:= f t; let L:= fderiv ℝ g; let M:= z*‖v‖; let B:=closedBall x M; have hM : 0≤M:= by unfold M; positivity
    have hx : x∈ B:=mem_closedBall_self hM; have hI : ‖(x+z • v)-x‖=M:= by rw [ add_sub_cancel_left,norm_smul,norm_of_nonneg hz.le ]
    have hj : (x+z • v)∈ B:= mem_closedBall_iff_norm.mpr hI.le
    have hL (p:E) (hp':p∈B): ‖ L p - L x‖≤ K*M  := ( (  convex_closedBall x M ).norm_image_sub_le_of_norm_hasFDerivWithin_le (f:=L) (fun p hp'=> ( ( hp.fits.sm t ).differentiable (by simp) p|>.hasFDerivAt.hasFDerivWithinAt )) (fun p hp'=> h t ht p ( closedBall_subset_closedBall (mul_le_of_le_one_left (norm_nonneg _) hy) hp' )) hx hp' ).trans ( mul_le_mul_of_nonneg_left (mem_closedBall_iff_norm.mp hp') hK.le )
    have hT := (convex_closedBall x M).norm_image_sub_le_of_norm_hasFDerivWithin_le' (f:=g) (φ:=L x) (fun p hp'=> ( ( hp.sm t ).differentiable (by simp) p |>.hasFDerivAt.hasFDerivWithinAt )) hL hx hj
    rw [hI,add_sub_cancel_left,map_smul] at hT; rw [dist_comm,dist_eq_norm]; change ‖z⁻¹ • (g (x+z • v) - g x) - L x v‖ ≤ _; rw [ ← show z⁻¹ • (g (x+z • v) - g x-z • (L x v)) = z⁻¹ • (g (x+z • v) - g x) - L x v from by rw [smul_sub, inv_smul_smul₀ hz.ne'], norm_smul,norm_of_nonneg (inv_pos.mpr hz).le ]; apply (mul_le_mul_of_nonneg_left hT (inv_pos.mpr hz).le).trans; unfold M; field_simp; nlinarith
variable [ TopologicalSpace I ][FiniteDimensional ℝ E]
lemma B_view {X:I→ E→L[ℝ] F}(h:∀ p:E,Continuous (fun i=> X i p)): Continuous X:= by
    let B:=Module.finBasis ℝ E; let Y i:F→L[ℝ] E→L[ℝ] F:= ContinuousLinearMap.smulRightL ℝ E F (( B.coord i ).toContinuousLinearMap); rw [show X=(fun x=> ∑ i:Fin ( Module.finrank ℝ E ), Y i ( X x ( B i ))) from ?_]; exact continuous_finsetSum _ (fun i _=> (Y i).continuous.comp (h (B i))); funext x; ext p; nth_rw 1 [← B.sum_repr p]; simp [Y, _root_.sum_apply]; simp_rw [← map_smul (X x), ← map_sum]; rw [ B.sum_repr ]
lemma Gym.jet_first (hp:Gym f)(hx:∀ p, Continuous (fun i=> f i p))(x:E): Continuous (fun i=> fderiv ℝ (f i) x ) := by
    apply B_view; intro v
    rw [continuous_iff_continuousAt]; intro i; let g (i:ℝ):= fderiv ℝ (f i) x v; let r:=‖i‖+1; obtain ⟨K,hK,h⟩:= hp.slope r (by unfold r; positivity) x v; apply Metric.continuousAt_iff'.mpr; intro ε hε; let z:=min (ε/(4*K)) 1; have hz:0<z:= by unfold z; positivity
    let H (i:ℝ):= z⁻¹ • ( f i (x+z • v)-f i x ); have hH : Continuous H:= ((hx _).sub (hx _)).const_smul _; have hd {t:ℝ}(ht:t∈Set.Icc (-r) r): dist (g t) (H t) ≤ ε/4:= by
       apply (h t ht z hz (min_le_right ..)).trans; apply (mul_le_mul_of_nonneg_left (min_le_left ..) hK.le).trans; exact le_of_eq (by field_simp)
    filter_upwards [lamp i,Metric.tendsto_nhds.mp (hH.tendsto i) (ε/2) (by positivity)] with t ht hD; obtain hd' := hd ht; obtain ht' := hd ( existsC i ); have he := dist_triangle4 (g t) (H t) (H i) (g i); rw [ dist_comm (H i) (g i) ] at he; change dist (g t) (g i) < _; linarith
lemma Gym.jet_c (hp:Gym f)(hx:∀ p:E, Continuous (fun i=> f i p))(x:E)(j:ℕ): Continuous (fun i=> iteratedFDeriv ℝ j (f i) x) := by
   induction j generalizing F f with
   | zero=> exact (continuousMultilinearCurryFin0 ℝ E F).symm.continuous.comp ( hx x )
   | succ j ih=> rw [show (fun i=> iteratedFDeriv ℝ (j+1) (f i) x )=_ from funext fun i=> iteratedFDeriv_succ_eq_comp_right]; exact (continuousMultilinearCurryRightEquiv' ℝ j E F).symm.continuous.comp (ih hp.fits (hp.jet_first hx))
end YM.FVA2.O.Tune
