import YM.XSpace.Shining
/-!
# Distribution line derivative identity (entered through test currency)

 To export an explicit answer even for the continuum triangle (its numeric normalization). Prove weak first derivative of D0 agrees with the a.e. function. (Take a lattice limit of the IBP!)
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Season
open Function Set Filter MeasureTheory Relief Sail Tide Playpen Trace Litter Octave Further.FreeCovariance.KP Lattice
open scoped Topology BigOperators Interval
variable {ι:Type}{L:Filter ι}{a:ι→ℝ}{x:ι→Cover}{u:E4} {A:Toe}{f:Breeze}
abbrev glass (φ:E4→ℝ)(a:ℝ)(w:Cover):= φ (actual a w)
lemma mercy (t:Axis)(φ:E4→ℝ)(h:ContDiff ℝ 1 φ)(s:Stage L a)(p:distance L a x u): Tendsto (fun i=>(a i)⁻¹ * η t (glass φ (a i)) (x i)) L (𝓝 (-(Maxwell.grad t φ u))):=by
  let v:= -basis t; let K:= fderiv ℝ φ u; let M(y:E4×ℝ):=∫ s:ℝ in 0..1, fderiv ℝ φ (y.1+(y.2*s) • v) v; have hc:= h.continuous_fderiv one_ne_zero; have hh:Continuous M:=by unfold M; apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'; unfold uncurry; fun_prop
  have he:= hh.continuousAt.tendsto.comp (p.prodMk_nhds s.zero); rw [show M (u,0)=-(Maxwell.grad t φ u) from by unfold M v; simp;rfl] at he; apply he.congr'; filter_upwards [s.good] with i hi; let z:= a i; let w:= actual z (x i); change M (w,z) = z⁻¹*(φ (actual z (x i-step t))-φ w); rw [Shade.offset_turn, show actual z (x i)-z • basis t=w+z • v by simp [w,v,sub_eq_add_neg] ]; have hd(s:ℝ): HasDerivAt (fun x:ℝ=> φ (w+(z*x) • v)) (z • fderiv ℝ φ (w+(z*s) • v) v) s:=by
    have ht : HasDerivAt (fun x:ℝ=> w+(z*x) • v) (z • v) s:= by simpa only [zero_add,mul_one] using! (hasDerivAt_const s w).add (((hasDerivAt_id' s).const_mul z).smul_const v)
    simpa only [map_smul] using! ((h.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt s ht)
  have hp : z*M (w,z)=φ (w+z • v)-φ w:=by change z • M (w,z)=_; unfold M; rw [← intervalIntegral.integral_smul, intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _=> hd x)]; simp; apply Continuous.intervalIntegrable; fun_prop
  rw [← hp, inv_mul_cancel_left₀ hi.ne']
variable (t:Axis)(φ:E4→ℝ)(h:ContDiff ℝ 1 φ)(H:HasCompactSupport φ)
include h H in
lemma payable : ∃ C:ℝ,0<C∧∀ p:ℝ,0<p→∀ x:Cover, ‖η t (glass φ p) x‖ ≤ C * p:=by
  obtain ⟨C,hC⟩ := (h.continuous_fderiv one_ne_zero).bounded_above_of_compact_support (H.fderiv ℝ); refine ⟨max C 1,lt_of_lt_of_le one_pos (le_max_right ..),fun p hp x=>?_⟩; let a:=actual p x; have hz:‖actual p (x-step t)-actual p x‖=p:=by rw [Shade.offset_turn,sub_right_comm,sub_self,zero_sub,norm_neg,norm_smul,Real.norm_of_nonneg hp.le,basis_norm,mul_one]
  change ‖φ _-φ _‖≤ _; refine ((convex_univ (E:=E4)).norm_image_sub_le_of_norm_fderiv_le (𝕜:=ℝ) (fun x _=>h.differentiable one_ne_zero x) (fun x _=> (hC x).trans (le_max_left C 1)) (y:=actual p (x-step t)) trivial trivial).trans_eq ?_; rw [hz]
include H in
lemma rims : ∃ C:ℝ,0<C ∧ ∀ x:E4, φ x ≠0 → ‖x‖≤ C:=by obtain ⟨C,h,hC⟩:= (show IsCompact (tsupport φ) from H).isBounded.subset_closedBall_lt 0 0; exact ⟨C,h,fun x hx=> dist_zero_right x ▸ Metric.mem_closedBall.mp (hC (subset_closure hx))⟩
include H in
lemma boundsT :∃ C:ℝ,0≤C∧∀ p:ℝ,0<p→p≤1→∀ x:Cover, (glass φ p x≠0∨glass φ p (x-step t)≠0)→p*pad x ≤ C:=by
  obtain ⟨C,hC,H⟩:= rims φ H; refine ⟨C+2,by positivity,fun p hp h x hx=>?_⟩; obtain ⟨ht,hv⟩:= Shade.size_actual hp x; unfold pad Drama.area; rcases hx with Hx|Hx; linarith [H _ Hx]; have hh:= H _ Hx; have hs:= Shade.offset_turn t x p; rw [hs] at hh; let v:= actual p x; have hx : ‖v‖≤ _:= norm_le_norm_sub_add v (p • basis t); rw [norm_smul,Real.norm_of_nonneg hp.le,basis_norm,mul_one] at hx; unfold v at hx; linarith
include H in
lemma glass_sum (A:Toe)(p:ℝ)(hp:0<p): Summable fun v:Cover=> A v*glass φ p v:=by
  classical obtain ⟨C,hC,H⟩:= rims φ H; apply summable_of_ne_finset_zero (s:=box ⌈C/p⌉₊); intro b hb; by_contra he; have hh:= H _ (right_ne_zero_of_mul he); apply hb; rw [box_rate]; have hv:= (Shade.size_actual hp b).1.trans hh; have ht:(reach b:ℝ)≤ C/p:= (le_div_iff₀ hp).2 (by linarith); exact_mod_cast ht.trans (Nat.le_ceil _)
end YM.XSpace.Season
