import YM.RG11Scheme.Hinge.Hertz

/-! Smooth cutoffs on the lattice integrated vertex. Boundary gradients include differing midpoint shifts. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 450000
namespace YM.RG11Scheme.Hinge
open Function Set Filter MeasureTheory Maxwell Pert Full Align Mesh Next.Rank.Radian Stencil Stencil.Shot Stencil.Point Lattice
open scoped BigOperators Classical ContDiff Topology
variable {E:Type} [NormedAddCommGroup E][NormedSpace ℝ E][CompleteSpace E]
variable {T : Itinerary} {V : Set E4} {a:E4→ E} {g:ℕ→ Cover→ E} {k:ℕ}

def pin (a:E4→ E)(h:ℝ)(u:E4)(x:Cover) := a (u+h • row x)
lemma single_pin (K:Axis)(hf:ContDiff ℝ ∞ a)(h:ℝ)(hh:0<h)(u:E4)(x:Cover):
    stride h K (pin a h u) x = ∫ t:ℝ in Ioc 0 1, pin (grad K a) h (u + t • h • basis K) x := by
   let p (t:ℝ):= u+t • h • basis K+h • row x
   have he : ContDiff ℝ ∞ (grad K a) := contDiff_iff_contDiffAt.mpr (fun i=> grad_smooth _ hf.contDiffAt (by simp))
   have hb : Continuous fun t:ℝ=>pin (grad K a) h (u+t • h • basis K) x := he.continuous.comp (f:=p) (show Continuous p from by unfold p;fun_prop)
   have hD t : HasDerivAt (a ∘ p) (h • pin (grad K a) h (u+t • h • basis K) x) t := by
      have hp t: HasDerivAt p (h • basis K) t := by
          simpa only [p, one_smul] using! ((((hasDerivAt_id' t).smul_const (h • basis K)).const_add u).add_const (h • row x))
      apply (HasFDerivAt.comp_hasDerivAt t ((hf.differentiable (by decide) (p t)).hasFDerivAt) (hp t)).congr_deriv
      exact map_smul _ _ _
   have ex := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:= (0:ℝ)) (b:=1) (fun t _=> hD t) ((hb.const_smul h).intervalIntegrable 0 1)
   rw [intervalIntegral.integral_of_le zero_le_one,integral_smul] at ex
   unfold stride pin
   simp only [Function.comp_apply, p, one_smul,zero_smul,add_zero] at ex
   rw [row_add,row_step,smul_add, ← add_assoc,add_right_comm u,←ex, smul_smul,inv_mul_cancel₀ hh.ne',one_smul]; rfl

omit [NormedSpace ℝ E] [CompleteSpace E] in
lemma measurable_route (D:List Axis) (F:ℝ→ Cover→E)(hF:∀ x,Continuous fun t=>F t x)(x:Cover): Continuous fun t=>go D (F t) x := by
   induction D generalizing x with| nil=>apply hF| cons i D IH=>exact (IH _).sub (IH _)
omit [CompleteSpace E] in
lemma route (D : List Axis) (F:ℝ→ Cover→E)(hF:∀ x,Continuous fun t=>F t x)(x:Cover):
     (go D (fun y=>∫ t:ℝ in Ioc 0 1,F t y) x) = ∫ t:ℝ in Ioc 0 1, go D (F t) x := by
   induction D generalizing x with
   | nil=> rfl
   | cons i D IH => simp only [onwards,IH]; rw [integral_sub]; exacts [((measurable_route D F hF _).continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self),((measurable_route D F hF _).continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self)]

lemma attached_point {u:ℕ→E4}{t:E4} (D:List Axis)(ha:ContDiff ℝ ∞ a)(h:ℕ→ℝ)(hu:∀ i,0<h i) (hh:Tendsto h atTop (𝓝 0))(p:ℕ→ Cover)(hx:Tendsto (fun i=> u i+ h i • row (p i)) atTop (𝓝 t)) : Tendsto (fun i=> ((h i)^D.length)⁻¹ • go D (pin a (h i) (u i)) (p i)) atTop (𝓝 (dV D a t)) := by
   induction D using List.reverseRecOn generalizing h p u a with
   | nil=> simpa only [List.length_nil,pow_zero,inv_one,one_smul,starting,dV,List.foldr_nil,pin, Function.comp_def] using ha.continuous.continuousAt.tendsto.comp hx
   | append_singleton D d IH=>
      let b:=grad d a
      let L:=D.length
      let f i (r:ℝ):= pin b (h i) (u i+r • h i • basis d)
      have hb : ContDiff ℝ ∞ b:=contDiff_iff_contDiffAt.mpr (fun x=> grad_smooth _ ha.contDiffAt (by simp))
      have hF i x : Continuous fun t=> f i t x := by unfold f pin; apply Continuous.comp hb.continuous _; fun_prop
      let F (i:ℕ) (r:ℝ):=((h i)^L)⁻¹ • go D (f i r) (p i)
      have hf i : Continuous (F i) := (measurable_route D _ (hF i) (p i)).const_smul _
      let μ:Measure ℝ:= volume.restrict (Ioc 0 1)
      have he (σ:ℕ→ℕ)(hσ:Tendsto σ atTop atTop)(τ:ℕ→ℝ)(z:ℝ)(he:Tendsto τ atTop (𝓝 z)) : Tendsto (fun i=>F (σ i) (τ i)) atTop (𝓝 (dV D b t)) := by
         refine IH hb (h ∘ σ) (fun v=>hu (σ v)) (hh.comp hσ) (p ∘ σ) (u:=fun i=>u (σ i)+τ i • h (σ i) • basis d) ?_
         simp_rw [show ∀ i,u (σ i)+ τ i • h (σ i) • basis d+(h ∘ σ) i • row ((p ∘ σ) i)= (u (σ i)+ h (σ i) • row (p (σ i)))+τ i • h (σ i) • basis d from fun i=>by simp only [Function.comp_apply]; abel]
         simpa only [zero_smul,smul_zero, add_zero,Function.comp_def] using ((hx.comp hσ).add (he.smul ((hh.comp hσ).smul_const (basis d))))
      have Hbound: ∃ C≥0, ∀ᶠ i:ℕ in atTop,∀ x:ℝ,x∈Icc 0 1→‖F i x‖≤C := by
         by_contra! he'
         have hv (i:ℕ):∃ j≥i,∃ x:ℝ,x∈Icc 0 1∧(i:ℝ)<‖F j x‖:= frequently_atTop.1 (he' (i:ℝ) (by positivity)) i
         choose Q hQ B hB K using hv
         obtain ⟨w,-,γ,hγ,Hγ⟩:= isCompact_Icc.isSeqCompact hB
         have hh:=hγ.tendsto_atTop
         have hz := he (Q ∘ γ) ((tendsto_atTop_mono (f:=id) hQ tendsto_id).comp hh) (B ∘ γ) w Hγ
         let R:=‖dV D b t‖+1
         obtain ⟨i,hi,L⟩:= ((hz.norm.eventually (ge_mem_nhds (lt_add_one _))).and ((tendsto_natCast_atTop_atTop.comp hh).eventually (eventually_ge_atTop R))).exists
         exact (not_lt_of_ge (hi.trans L)) (K (γ i))
      obtain ⟨C,-,H⟩:=Hbound
      letI : IsFiniteMeasure μ := by unfold μ; exact MeasureTheory.isFiniteMeasure_restrict.mpr (by simp) -- check
      have hv := tendsto_integral_filter_of_dominated_convergence (μ:=μ) (F:=F) (f:=fun _=>dV D b t) (fun _=>C) (Eventually.of_forall (fun i=>(hf i).aestronglyMeasurable)) (H.mono (fun i hi=> ae_restrict_of_forall_mem measurableSet_Ioc (fun x hx=>hi x (Ioc_subset_Icc_self hx)))) (integrable_const _) (Eventually.of_forall fun x=> he _ tendsto_id _ x tendsto_const_nhds)
      rw [show (∫ _:ℝ,dV D b t ∂μ)=dV D b t from ?_] at hv
      · rw [dV_append]; apply hv.congr; intro i; change (∫ t:ℝ in Ioc 0 1,F i t)=_; rw [list_append D d (h i) _ (hu i).ne',show stride _ _ _ = _ from funext (single_pin d ha (h i) (hu i) (u i)), route D _ (hF i)]; exact integral_smul ..
      dsimp only [μ]; rw [setIntegral_const]; norm_num
lemma sample (T:Itinerary) (ha:ContDiff ℝ ∞ a): Works T univ (fun i x=> a (incVec (T.gap i) x)) a k := by
   refine ⟨fun _ _=>ha.contDiffAt,?_⟩;intro σ hs x hx p he D hd;simp only [inc_row] at he
   simpa only [show ∀ s:ℝ,pin a s 0=fun x=> a (incVec s x) from fun s=>by funext; simp [pin,inc_row],Function.comp_apply] using! attached_point (u:=fun _=>0) D ha (T.gap ∘ σ) (fun i=>T.positive _) (T.cutoff.comp hs) p (t:=x) (by simp only [Function.comp_def,zero_add]; exact he)
end YM.RG11Scheme.Hinge
