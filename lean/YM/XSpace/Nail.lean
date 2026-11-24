import YM.XSpace.ShellEcho

/-!
# Cutoff shell fees (geometry of the expanding difference support)
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Shade
open Filter Function Set Prelude Future Mu Drama Lows Lattice Sail Further.FreeCovariance.KP Playpen Trace Chart2 Scale
open scoped Topology BigOperators Interval ContDiff
variable {G:Gauge} {ι:Type} {L:Filter ι}{b d:ℕ}
variable (X:Axis)(c:Cut)

def turn (p:ℝ):Mark:=sibling (outfit c p) X
lemma turning (p:ℝ)(x:Cover): turn X c p x=pace c p (x-step X)-pace c p x:=by rw [turn,sibling_at,outfit_eq,outfit_eq]
lemma offset_turn (x:Cover)(p:ℝ):actual p (x-step X)=actual p x-p • basis X:=by
  have he:= Litter.rcast_step_add (x-step X) X; rw [sub_add_cancel] at he; unfold actual; rw [he, smul_add,add_sub_cancel_right]
private lemma remote (r:ℝ)(t:Cover)(hr:0<r)(h:turn X c r t≠0): ‖actual r t‖ ≤ c.rOut+r ∧ c.rIn ≤ ‖actual r t‖+r:=by
  rw [turning] at h; let a:=actual r t; let b:= actual r (t-step X); have hp : b=a-r • basis X:= offset_turn X ..; have hb:‖b-a‖ = r:=by rw [hp,sub_right_comm,sub_self,zero_sub,norm_neg,norm_smul,Real.norm_of_nonneg hr.le,basis_norm,mul_one]
  have hu : ‖b‖≤ ‖a‖+r := by have hw:= norm_sub_norm_le b a; linarith
  constructor
  · by_cases ht: pace c r t ≠ 0; · exact (tag c r t ht).2.le.trans (le_add_of_nonneg_right hr.le)
    have hx: pace c r (t-step X) ≠ 0:=fun p=> h (by rw [p,not_not.mp ht,sub_self]); have hw : ‖b‖< c.rOut:=(tag c _ _ hx).2; change ‖a‖ ≤ _; linarith [norm_sub_norm_le a b,norm_sub_rev b a]
  by_contra! hz; change ‖a‖+r< _ at hz; exact h (by rw [cut_inside c _ _ hr (by change ‖b‖ ≤ _; linarith), cut_inside c t r hr (by change ‖a‖ ≤ _; linarith),sub_self])
lemma seam_fees :∃ b B C r:ℝ, 0<b∧1≤B∧0≤C∧0<r∧ ∀ p:ℝ,0<p→p≤r→∀ x:Cover,turn X c p x≠0→ b≤ p*area x ∧ p*area x ≤ B ∧ ‖turn X c p x‖ ≤ C*p:=by
  let s:=min 1 (c.rIn/2); let Q:= Metric.closedBall (0:E4) (c.rOut+2*s); obtain ⟨k,H⟩:= LocallyLipschitzOn.exists_lipschitzOnWith_of_compact (f:=fun x=>c x) (isCompact_closedBall (0:E4) (c.rOut+2*s)) (by
    intro x hx; have hc: ContDiffAt ℝ 1 (fun x=> c x) x:=c.contDiff.contDiffAt; obtain ⟨B,t,ht,H⟩:=hc.exists_lipschitzOnWith; exact ⟨B,t,nhdsWithin_le_nhds ht,H⟩)
  refine ⟨c.rIn/4,c.rOut+2,k,s,?_,?_,k.property,lt_min one_pos (half_pos c.rIn_pos),fun p hp h x hx=>?_⟩
  · linarith [c.rIn_pos]
  · linarith [c.rOut_pos]
  have hr := remote X c p x hp hx; let y:=actual p (x-step X); let z:=actual p x; have he : p≤1∧p≤c.rIn/2:= le_min_iff.mp h; obtain ⟨a,b⟩:=size_actual hp x; refine ⟨?_,?_,?_⟩
  · unfold area; nlinarith [hr.2, he.2]
  · unfold area; nlinarith [hr.1,he.1]
  have hz: z∈Q:=Metric.mem_closedBall.mpr (by rw [dist_zero_right]; change ‖actual _ _‖ ≤ _; linarith [hr.1]); have hu: dist y z=p:= by unfold y z; rw [dist_eq_norm,offset_turn,sub_right_comm,sub_self,zero_sub,norm_neg,norm_smul, Real.norm_of_nonneg hp.le, basis_norm,mul_one]
  have hy:= hr.1
  have hZ:y∈Q:=Metric.mem_closedBall.mpr (by rw [dist_zero_right]; apply (norm_le_norm_sub_add y z).trans; rw [← dist_eq_norm,hu]; unfold z; linarith)
  have hd:=H.dist_le_mul y hZ z hz; rw [turning,pace,pace, if_pos hp, if_pos hp, ← Complex.ofReal_sub, Complex.norm_real, ← dist_eq_norm]; simpa only [hu] using hd

-- strict differentiability on moving centers

lemma saw {A:ι→ℝ}(S:Tendsto A L (𝓝 0))(he:∀ᶠ i in L,0<A i){x:ι→Cover}{z:E4}(hz:Tendsto (fun i=>actual (A i) (x i)) L (𝓝 z)):
    Tendsto (fun i=> (A i:ℂ)⁻¹ * turn X c (A i) (x i)) L (𝓝 (↑( (fderiv ℝ (fun x=>c x) z) (-basis X)):ℂ)):=by
  let v:= -basis X; let K:= fderiv ℝ (fun x=>c x) z; let f i:=actual (A i) (x i); let g i:=actual (A i) (x i-step X)
  have hc : ContDiff ℝ 1 (fun x=> c x):= c.contDiff; have hd:= hc.continuous_fderiv one_ne_zero
  let D(y:E4×ℝ):=∫ s:ℝ in 0..1,fderiv ℝ (fun x=>c x) (y.1+(y.2*s) • v) v
  have hD:Continuous D:= by unfold D; apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'; unfold uncurry; fun_prop
  have hez:D (z,0)=K v:=by simp [D,K]
  have H:=hD.continuousAt.tendsto.comp (hz.prodMk_nhds S); rw [hez] at H; refine (Complex.continuous_ofReal.continuousAt.tendsto.comp H).congr' ?_
  filter_upwards [he] with i hi; let p:= A i; let w:=f i; rw [turning,pace,pace,if_pos hi,if_pos hi,← Complex.ofReal_sub,← Complex.ofReal_inv,← Complex.ofReal_mul]; apply congr_arg ((↑):ℝ→ℂ)
  change D (w,p)= p⁻¹*(c (actual _ (_-step X))-c w); rw [offset_turn,show actual (A i) (x i)-A i • basis X=w+p • v by simp [f,w,p,v,sub_eq_add_neg] ]; have hh(s:ℝ): HasDerivAt (fun x:ℝ=> c (w+(p*x) • v)) (p • fderiv ℝ (fun x=> c x) (w+(p*s) • v) v) s:=by
    have h : HasDerivAt (fun x:ℝ=> w+(p*x) • v) (p • v) s:= by simpa only [zero_add,mul_one] using! (hasDerivAt_const s w).add (((hasDerivAt_id' s).const_mul p).smul_const v)
    simpa only [map_smul] using! ((hc.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt s h)
  have hp : p*D (w,p)=c (w+p • v)-c w:=by
    change p • D (w,p)=_; unfold D; rw [← intervalIntegral.integral_smul, intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _=> hh x)]; simp; apply Continuous.intervalIntegrable; fun_prop
  rw [← hp, inv_mul_cancel_left₀ hi.ne'] -- p mismatch
end YM.XSpace.Shade
