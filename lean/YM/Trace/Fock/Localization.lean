import YM.Trace.Fock.Transverse

/-! Vacuum relative distributions in positive and negative shell evolution after removing
projections. The multiplying Fourier tests are signed exactly as in (nff).
-/
noncomputable section
namespace YM.Trace.Shell
open YM Boundary Function Filter MeasureTheory Set Complex
open scoped BigOperators ENNReal InnerProductSpace Topology ContDiff Pointwise
variable {m n : ℕ}
set_option maxHeartbeats 280000
set_option autoImplicit false
noncomputable def bundle (K : @Angle m n) (a : Fin n→Test4) : @Mixed n m := fun j z => if K j = z then a j else 0
lemma bundle_bar (K : @Angle m n) (a) : barSlots (bundle K a)=bundle K (fun i=>Probe.bar (a i)) :=
   funext (fun i=> funext (by intro k; by_cases h:k=K i; subst k; simp [bundle,barSlots]; simp [bundle,barSlots,Ne.symm h])) -- proof h not Ne
noncomputable def mill (x : Cords n) := ∏ i, ‖x i‖
lemma nonnegative_mill (x : Cords n) : 0≤ mill x := Finset.prod_nonneg (fun _ _=> norm_nonneg _)
noncomputable def testedPlus (a : Fin n→Test4) (x:Cords n) := ∏ i, plus (a i) (ray (x i))
noncomputable def testedMinus (a : Fin n→Test4) (x:Cords n) := ∏ i, Probe.hat (a i) (ray (x i))
lemma plus_bar_hat (a : Test4) (u) : star (plus (Probe.bar a) u)=Probe.hat a u := by rw [plus_bar,star_star,plus_eq_hat,neg_neg]
lemma explicit_spread (K : @Angle m n) (a) (x : Cords n) (j:@Angle m n) : spread (bundle K a) x j = if K=j then (mill x:ℂ)*testedPlus a x else 0 := by
     unfold spread mill testedPlus; split_ifs with h
     · rw [Finset.prod_mul_distrib,h,Complex.ofReal_prod]; simp [bundle] -- cannot rw K
     obtain ⟨t,ht⟩ := Function.ne_iff.mp h -- name
     exact Finset.prod_eq_zero (Finset.mem_univ t) (by simp [bundle,ht])
lemma explicit_bar (K : @Angle m n) (a) (x : Cords n) (j:@Angle m n) : star (spread (barSlots (bundle K a)) x j) = if j=K then (mill x:ℂ)*testedMinus a x else 0 := by
     rw [bundle_bar, explicit_spread]; by_cases h : K=j
     · rw [h,if_pos rfl,if_pos rfl, star_mul', RCLike.star_def, conj_ofReal]; unfold testedPlus testedMinus
       rw [map_prod]; congr 1; exact Finset.prod_congr rfl (fun i _=> plus_bar_hat ..)
     rw [if_neg h, if_neg (Ne.symm h),star_zero]
variable (v : Test4→L[ℂ] Sum m) (hv : FieldImage v)
noncomputable def kernelA (K : @Angle m n) (a : Fin n→Test4) (x : Cords n) := (mill x:ℂ) * (fullWave v n x K) * testedMinus a x
noncomputable def kernelB (K : @Angle m n) (a : Fin n→Test4) (x : Cords n) := (mill x:ℂ) * star (fullWave v n x K) * testedPlus a x
private lemma plainDiagonal (kind:ℂ) (z : Fiber m n) (k) : ∑ j, (if j=k then kind else 0) * z j = kind * z k := by
     classical exact (by apply Eq.trans (Finset.sum_eq_single k _ _) _; intros i _ hi; simp [hi]; simp; simp) -- check instead sum_eq_single
@[fun_prop] lemma measurable_mill (n) : Measurable (@mill n) := by unfold mill; fun_prop
@[fun_prop] lemma measurable_testedPlus (a : Fin n→Test4) : Measurable (testedPlus a) := (Finset.measurable_fun_prod _ (fun k _=> ((plus (a k)).continuous.measurable.comp (continuous_ray.measurable.comp (measurable_pi_apply ..)))) )
@[fun_prop] lemma measurable_testedMinus (a : Fin n→Test4) : Measurable (testedMinus a) := Finset.measurable_fun_prod _ (fun k _=> ((Probe.hat (a k)).continuous.measurable.comp (continuous_ray.measurable.comp (measurable_pi_apply ..))))
omit hv in
@[fun_prop] lemma measurable_A (a : Fin n→Test4) (k : @Angle m n) : Measurable (kernelA v k a) := by
     unfold kernelA; refine (measurable_ofReal.comp (measurable_mill ..)|>.mul ((PiLp.continuous_apply ..).measurable.comp (fullWave_meas v ..))).mul (measurable_testedMinus ..)
omit hv in
@[fun_prop] lemma measurable_B (a : Fin n→Test4) (k : @Angle m n) : Measurable (kernelB v k a) := by
     unfold kernelB; refine (measurable_ofReal.comp (measurable_mill ..)|>.mul (continuous_star.measurable.comp ((PiLp.continuous_apply ..).measurable.comp (fullWave_meas v ..)))).mul (measurable_testedPlus ..)

include hv in
lemma plainLeft (a : Fin n→Test4) (k : @Angle m n) (f : Test4) (hc : CC f) : pairLeft (v f n) (bundle k a) = ∫ x, plus f (total x) * kernelA v k a x ∂νpow n := by
    change inner ℂ (several n m _) _ = _; rw [lp_inner]
    have ht := fullWave_of_CC v hv f hc n
    refine integral_congr_ae ((several_coe_eq (barSlots (bundle k a))|>.and (ht.and (directTransverse v hv _))) |>.mono fun z hZ => ?_ )
    dsimp only [kernelA] at *
    rw [hZ.1,hZ.2.1,inner_smul_right,plain_inner _ _ _ hZ.2.2]
    simp_rw [explicit_bar]; rw [plainDiagonal]; ring
include hv in
lemma plainRight (a : Fin n→Test4) (k : @Angle m n) (f : Test4) (hc : CC f) : pairRight (v f n) (bundle k a) = ∫ x, star (plus f (total x)) * kernelB v k a x ∂νpow n := by
    change inner ℂ _ (several n m _) = _; rw [lp_inner]
    have ht := fullWave_of_CC v hv f hc n
    refine integral_congr_ae ((several_coe_eq (bundle k a)|>.and (ht.and (directTransverse v hv _))) |>.mono fun z hZ => ?_ )
    dsimp only [kernelB] at *
    change inner ℂ _ _= _
    rw [hZ.1,hZ.2.1,inner_smul_left,plain_inner_flip _ _ _ hZ.2.2,starRingEnd_apply]; congr 1
    classical
    refine Eq.trans (Finset.sum_eq_single k (fun b _ hb=> ?_) (by simp)) ?_
    · rw [explicit_spread, if_neg (Ne.symm hb),mul_zero]
    rw [explicit_spread, if_pos rfl]; ring
private lemma compact_bar {f : Test4} (hc : CC f) : CC (Probe.bar f) := hc.comp_left (map_zero (starAddEquiv : ℂ ≃+ ℂ))
include hv in
lemma kernels_exchange (a : Fin n→Test4) (hC : ∀ i, CC (a i)) (hS : ∀ i, tsupport (a i) ⊆ Mink.spacelike) : ∀ k : @Angle m n,
    ∃ r > 0, ∀ f : Test4, tsupport f ⊆ Metric.ball 0 r →
      (∫ x, plus f (total x) * kernelA v k a x ∂νpow n) = ∫ x, Probe.hat f (total x) * kernelB v k a x ∂νpow n := by
   intro k
   have hz : HasCompactSupport (fun _:E4 =>(0:ℂ)) := by change HasCompactSupport (0:E4→ℂ); exact HasCompactSupport.zero
   have hc (i j) : CC (bundle k a i j) := by by_cases hj:k i=j; rw [bundle,if_pos hj]; exact hC i; rw [bundle,if_neg hj]; exact hz
   have hS (i : Fin n) : supportE (bundle k a i) ⊆ Mink.spacelike := by
      unfold supportE; refine iUnion_subset (fun j => ?_); by_cases h:k i=j
      · rw [bundle,if_pos h]; exact hS i
      rw [bundle,if_neg h]; change tsupport (0:E4→ℂ) ⊆ _; simp
   obtain ⟨s,hs,ht⟩ := exchange_terms v hv (bundle k a) hc hS
   refine ⟨s,hs,fun f hf=> ?_⟩
   have hc : CC f := isCompact_closedBall (0:E4) s |>.of_isClosed_subset isClosed_closure (hf.trans Metric.ball_subset_closedBall)
   simp_rw [← plus_bar_hat]
   exact (plainLeft v hv a k f hc).symm.trans ((ht f hf).trans (plainRight v hv a k _ (compact_bar hc))) -- syntax
lemma mill_le (x : Cords n) : mill x ≤ weight n x := ((Finset.prod_le_prod (fun i _=>norm_nonneg _) (fun i (_: i∈Finset.univ)=> show ‖x i‖ ≤ (1+‖x‖) from (norm_le_pi_norm ..).trans (by linarith))).trans_eq (by simp [weight]))
lemma shell_cost_n (f : Test4) {p : E4} {r : Mom} (hp : ‖r‖≤‖p‖) (k : ℕ) : ‖plus f p‖ ≤ orderCost (plus f) k * 2^k * (weight k r)⁻¹ := (weighted_test ..).trans
    (by refine mul_le_mul_of_nonneg_left ((inv_le_inv₀ (weight_pos ..) (weight_pos ..)).2 (by unfold weight; gcongr)) (mul_nonneg (orderCost_nonneg ..) (by positivity)))
noncomputable def locatedCost (a : Fin n→Test4) (k) := ∏ i, orderCost (plus (a i)) k * 2^k
lemma bound_positive (a : Fin n→Test4) (x : Cords n) (k : ℕ) : ‖testedPlus a x‖ ≤ locatedCost a k * packing x k :=
   le_trans (le_of_eq (norm_prod ..)) (by unfold locatedCost packing; rw [← Finset.prod_mul_distrib]; exact Finset.prod_le_prod (fun _ _=> norm_nonneg _) (fun i _=> shell_cost_n _ (norm_ray _) _))
lemma bound_negative (a : Fin n→Test4) (x : Cords n) (k : ℕ) : ‖testedMinus a x‖ ≤ locatedCost a k * packing x k :=
   le_trans (le_of_eq (norm_prod ..)) (by unfold locatedCost packing; rw [← Finset.prod_mul_distrib]; exact Finset.prod_le_prod (fun _ _=> norm_nonneg _) (by intro i _; rw [show Probe.hat (a i) (ray (x i))=plus (a i) (-(ray (x i))) by simp [plus_eq_hat]]; exact shell_cost_n _ (by rw [norm_neg]; exact norm_ray (x i)) _))
include hv in
lemma kernel_integrable (a : Fin n→Test4) (k : @Angle m n) : Integrable (kernelA v k a) (νpow n) ∧ Integrable (kernelB v k a) (νpow n) := by
    obtain ⟨s,hs⟩ := all_moments v hv n n
    let h' := hs.mul_const (locatedCost a s)
    have hh : ∀ x : Cords n, ‖fullWave v _ x k‖≤‖fullWave v _ x‖ := fun _ => PiLp.norm_apply_le ..
    constructor
    · refine h'.mono' (measurable_A  v a k|>.aestronglyMeasurable) (.of_forall (fun x : Cords n => ?_))
      unfold kernelA; simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (nonnegative_mill x)]
      calc _ ≤ _ := mul_le_mul (mul_le_mul (mill_le x) (hh x) (by positivity) (by exact (weight_pos n x).le)) (bound_negative a x s) (by positivity)
               (mul_nonneg (by exact (weight_pos n x).le) (norm_nonneg _))
           _ = _ := by ring
    · refine h'.mono' (measurable_B  v a k|>.aestronglyMeasurable) (.of_forall (fun x : Cords n => ?_))
      unfold kernelB; simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (nonnegative_mill x),star_def,norm_conj]
      calc _ ≤ _ := mul_le_mul (mul_le_mul (mill_le x) (hh x) (by positivity) (by exact (weight_pos n x).le)) (bound_positive a x s) (by positivity)
               (mul_nonneg (by exact (weight_pos n x).le) (norm_nonneg _))
           _ = _ := by ring
private lemma shrink_support {f : Test4} (h : CC f) (t : ℝ) (ht : 0<t) (r : ℝ) (hr : 0<r) : ∀ᶠ t:ℝ in atTop, tsupport (normalized f t) ⊆ Metric.ball 0 r := by
   obtain ⟨M,hM⟩ := h.isBounded.subset_closedBall 0
   filter_upwards [eventually_gt_atTop (M/r),eventually_gt_atTop (0:ℝ)] with s hs hZ
   have hM' : ∀ x, f x≠0 → ‖x‖≤M := fun x hx=> by simpa using (hM (subset_tsupport (f:=f) hx)) -- coerce
   apply (closure_minimal (t:=Metric.closedBall 0 (M/s)) ?_ Metric.isClosed_closedBall).trans (Metric.closedBall_subset_ball ?_)
   · intro p hp; rw [Function.mem_support, normalized_eq _ hZ] at hp; have hpos := hM' (s • p) (fun he=> hp (by simp only [he,smul_zero])); rw [norm_smul,Real.norm_eq_abs,abs_of_pos hZ] at hpos
     exact Metric.mem_closedBall.mpr (by rw [dist_zero_right,le_div_iff₀ hZ]; linarith)
   rw [div_lt_iff₀ hZ]; exact lt_of_lt_of_le (b:=r*s) (by nlinarith [(div_lt_iff₀ hr).1 hs]) le_rfl

private lemma shrunk_limit (a : E4) : Tendsto (fun t:ℝ=> plus (normalized (initial E4) t) a) atTop (𝓝 1) := by
     have ht : Tendsto (fun t:ℝ=> (t⁻¹) • a) atTop (𝓝 (0:E4)) := by simpa using Filter.Tendsto.smul_const (tendsto_inv_atTop_zero (𝕜 := ℝ)) a
     exact Tendsto.congr' (eventually_gt_atTop (0:ℝ) |>.mono fun t ht => (plus_normalized (initial E4) ht a).symm) (by simpa only [plus_initial] using! ((plus (initial E4)).continuous.tendsto 0 |>.comp ht))
private lemma shrinking_tests {X : Type*} [MeasurableSpace X] {μ : Measure X} (G : X→E4) (hm : Measurable G) (A : X→ℂ) (hA : Integrable A μ) : Tendsto (fun (t:ℝ) =>
     (∫ p, plus (normalized (initial E4) t) (G p) * A p ∂μ)) atTop (𝓝 (∫ p, A p ∂μ)) := by
     refine tendsto_integral_filter_of_dominated_convergence (fun x=>smearCost (initial E4) * ‖A x‖) (.of_forall fun r:ℝ=> ((plus (normalized ..)).continuous.measurable.comp hm |>.aestronglyMeasurable.mul hA.aestronglyMeasurable)) (eventually_gt_atTop 0 |>.mono fun t (ht:0<t) => .of_forall fun x=> ?_) (hA.norm.const_mul _)
       (.of_forall fun x=> by simpa using ((shrunk_limit (G x)).mul_const (A x)))
     have H x := SchwartzMap.norm_le_seminorm ℂ (plus (initial E4)) x -- smearCost by def
     rw [norm_mul]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); rw [plus_normalized _ ht]; exact H _

include hv in
lemma kernel_match (a : Fin n→Test4) (hC : ∀ i, CC (a i)) (hS : ∀ i, tsupport (a i) ⊆ Mink.spacelike) : ∀ k : @Angle m n, (∫ x, kernelA v k a x ∂νpow n) = ∫ x, kernelB v k a x ∂νpow n := by
   intro k
   have H₁ := shrinking_tests (total (n:=n)) (continuous_total _).measurable (kernelA v k a) (kernel_integrable v hv _ _).1
   have H₂ := shrinking_tests (fun x:Cords n=>-(total x)) (by fun_prop) (kernelB v k a) (kernel_integrable v hv _ _).2
   apply tendsto_nhds_unique_of_eventuallyEq H₁ H₂
   obtain ⟨r,hr,ht⟩ := kernels_exchange v hv a hC hS k
   refine (shrink_support (f:=initial E4) initial_CC 1 zero_lt_one r hr).mono fun s hs=>?_;
   simpa only [plus_eq_hat (normalized (initial E4) s) (-(total _)),neg_neg] using ht _ hs
end YM.Trace.Shell
