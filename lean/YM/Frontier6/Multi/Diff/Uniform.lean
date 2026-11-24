import YM.Frontier6.Multi.Diff.Transfer

/- Uniform orbit differentiability. Use priced versions separately later. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Road
open Function Filter Set Metric MergeProof.Ribbons MergeProof.Acme
open scoped Topology BigOperators ContDiff Classical
variable {J E:Type*}[TopologicalSpace J][CompactSpace J][NormedAddCommGroup E][NormedSpace ℝ E]
lemma derives_roll {F U:ℝ→ C(J,E)}{x:ℝ}(he:ContinuousAt U x)
   (hy:∀ᶠ y in 𝓝 x,∀ j:J, HasDerivAt (fun y=> F y j) (U y j) y): HasDerivAt F (U x) x:=by
   rw [hasDerivAt_iff_tendsto_slope]; refine Metric.tendsto_nhds.mpr fun ε hε=>?_
   let a:= ε/2; have ha:0<a:=half_pos hε
   obtain ⟨δ,hδ,hh⟩:= Metric.mem_nhds_iff.mp (Eventually.and (he.preimage_mem_nhds (ball_mem_nhds (U x) ha) : ∀ᶠ y in 𝓝 x,U y∈ball (U x) a) hy)
   filter_upwards [ (eventually_nhdsWithin_of_eventually_nhds (show ∀ᶠ y in 𝓝 x, y∈ ball x δ from ball_mem_nhds _ hδ)), self_mem_nhdsWithin] with y hi he
   let W:= slope F x y-U x
   rw [dist_eq_norm]; refine lt_of_le_of_lt (show ‖W‖ ≤ a from (ContinuousMap.norm_le _ ha.le).mpr ?_) (half_lt_self hε); intro j
   let v(z:ℝ):= F z j - z • U x j; let f(z:ℝ):= U z j - U x j
   have hL(k)(hk:k∈ball x δ): HasDerivWithinAt v (f k) (ball x δ) k:=by
       refine ((hh hk|>.2 j).sub (g':= U x j) (g:=fun t:ℝ=>t • U x j) ?_).hasDerivWithinAt -- arg name f'? check
       simpa using! ((ContinuousLinearMap.toSpanSingleton ℝ (U x j)).hasDerivAt (x:=k))
   have hg(k)(hk:k∈ ball x δ):‖f k‖≤ a:=by
      refine ((ContinuousMap.norm_le (U k - U x) ha.le).mp ?_ j); exact (dist_eq_norm (U k) (U x)) ▸ (hh hk|>.1 : dist (U k) (U x) < a).le
   have hs:= Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (𝕜:=ℝ) hL hg (convex_ball x δ) (mem_ball_self hδ) hi
   have hx:y-x≠0:= sub_ne_zero.mpr he -- notation
   have hW:W j = (y-x)⁻¹ • (v y-v x):=by
        change (y-x)⁻¹ • (F y j-F x j)- U x j= _
        rw [show v y-v x= (F y j-F x j)-(y-x) • U x j from (by unfold v; rw [sub_smul]; abel)]; simp only [smul_sub, inv_smul_smul₀ hx]
   rw [hW,norm_smul, norm_inv]
   refine (mul_le_mul_of_nonneg_left hs (by positivity)).trans_eq ?_; rw [mul_comm a,← mul_assoc,inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx),one_mul]
end YM.Frontier6.Road
