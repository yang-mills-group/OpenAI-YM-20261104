import YM.Juniper.LocalAtlas.Pure
/-!
 # local logarithm on full numerator jet

 Norm transport in same width. `Wallet` quantity controls smooth quotient
 reexpression. Não arbitrarily require E prediction positivity outside receipt.
 `Log0` is secant *function* with removable singularities; needed for operator
 norms at full graph order, avoid spending one missing Taylor power at derivatives.
 -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.LocalAtlas
open MeasureTheory Set Function Metric Filter
open PhysicalNext.Repeat Lantern
open ConnectedActivityE6 Blaze Brush
open Work.G05 WilsonStartup Analysis Tensor
open scoped Classical Topology ContDiff BigOperators MatrixOrder Interval ENNReal
variable {E : Type} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
    {n k:ℕ}{D C v a b : ℝ} {f r:E→ℝ} {x:E}
private def mixF (z:ℝ × ℝ) (t:ℝ) := z.1+t*(z.2-z.1)
private def sec (z : ℝ×ℝ) := ∫ t in Set.Ioc (0:ℝ) 1,(mixF z t)⁻¹
private lemma sign (z : ℝ×ℝ)(t : ℝ)(h:0< z.1)(he:0< z.2)(ht:t∈Icc (0:ℝ) 1): 0 < mixF z t:= by
  unfold mixF; by_cases hy:z.1 ≤ z.2
  · exact add_pos_of_pos_of_nonneg h (mul_nonneg ht.1 (sub_nonneg.mpr hy))
  nlinarith only [he,mul_le_mul_of_nonneg_right ht.2 (sub_nonneg.mpr (not_le.mp hy|>.le))]
private lemma secant (z w:ℝ) (hz:0<z)(hw:0<w): Real.log w-Real.log z=(w-z)*sec (z,w):=by
    let u:= mixF (z,w); let f(t:ℝ):= Real.log (u t)
    let S:=Set.uIcc (0:ℝ) 1; have h t (ht:t∈S):0< u t:= sign _ t hz hw (by rwa [←uIcc_of_le zero_le_one]) -- S not defeq bc rwa ht stuck
    let w'(t:ℝ):=(w-z)*(u t)⁻¹; have he t (ht:t∈ S): HasDerivAt f (w' t) t :=by
      have hv:HasDerivAt u (w-z) t:= by simpa only [one_mul] using! ((((hasDerivAt_id' t).mul_const (w-z)).const_add z))
      exact (hv.log (h t ht).ne').congr_deriv (by unfold w'; ring)
    have hu: ContinuousOn w' S:= continuousOn_const.mul ((show Continuous u by unfold u mixF; fun_prop).continuousOn.inv₀ (fun t ht=>(h t ht).ne'))
    have hv:= intervalIntegral.integral_eq_sub_of_hasDerivAt he hu.intervalIntegrable; rw [intervalIntegral.integral_of_le zero_le_one] at hv; unfold w' f u mixF at hv; rw [integral_const_mul] at hv; simpa [sec,mixF] using hv.symm

private lemma sec_smooth (k:ℕ)(x:ℝ × ℝ)(hx: 0 < x.1)(hy:0<x.2): ContDiffAt ℝ (k:WithTop ℕ∞) sec x := by
   let S:= Set.Icc (0:ℝ) 1
   let P:= Set.Ioo (x.1/2) (x.1*2) ×ˢ Set.Ioo (x.2/2) (x.2*2)
   let T:= Set.Icc (x.1/2) (x.1*2) ×ˢ Set.Icc (x.2/2) (x.2*2)
   have He : P ⊆ T := Set.prod_mono Set.Ioo_subset_Icc_self Set.Ioo_subset_Icc_self
   have hh : ∀ᶠ y in 𝓝 x, y∈T:= mem_of_superset ((isOpen_Ioo.prod isOpen_Ioo).mem_nhds (show x∈P from ⟨by constructor <;> linarith,by constructor<;> linarith⟩)) He
   let V(y:ℝ×ℝ):= S.indicator (fun t:ℝ=>(mixF y t)⁻¹)
   let F(y:(ℝ×ℝ)×ℝ):=(mixF y.1 y.2)⁻¹
   obtain ⟨C,hC,hQ⟩:= Brush.compact (f:=F) (k:=k) ((isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc : IsCompact (T ×ˢ S)) (fun z hz=>(by unfold F mixF; apply ContDiffAt.inv; fun_prop; exact (sign _ _ ((half_pos hx).trans_le hz.1.1.1) ((half_pos hy).trans_le hz.1.2.1) hz.2).ne'))
   let μ:= (volume (α:=ℝ)).restrict (Ioc 0 1); letI:IsFiniteMeasure μ:= by unfold μ; infer_instance
   have hk : Meristem V x μ k := by
     refine (Meristem.points V μ ⟨fun _=>C,integrable_const _, hh.mono (fun y hy t=> ?_)⟩ (hh.mono fun y he=>?_)).1 -- two placeholders
     · by_cases ht:t∈S; swap
       · exact ((Brush.certified zero_le_one (0:ℝ)).climb (by simpa using hC.le) le_rfl).shimmy (Eventually.of_forall fun _=> Set.indicator_of_notMem ht _)
       let R:= ContinuousLinearMap.inl ℝ (ℝ×ℝ) ℝ
       have hp (a:ℝ×ℝ) : ((0:ℝ×ℝ),t) + R a=(a,t):=by simp [R]
       apply (Lantern.skim (f:=F) (P:=R) (y:=(0,t)) y (by rw [hp]; exact hQ _ ⟨hy,ht⟩) (ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x=>by simp [R])).shimmy
       exact Eventually.of_forall fun y=> by dsimp only; rw [hp]; exact Set.indicator_of_mem ht _
     exact (show Measurable fun t:ℝ=> (mixF y t)⁻¹ by unfold mixF; fun_prop).indicator (measurableSet_Icc)
   apply hk.calls.1.congr_of_eventuallyEq ?_
   refine Eventually.of_forall fun z=> ?_; symm; exact integral_congr_ae ( (ae_restrict_mem (μ:=volume) (s:=Ioc (0:ℝ) 1) measurableSet_Ioc).mono fun t ht => Set.indicator_of_mem (Ioc_subset_Icc_self ht) _)

structure Treasury (K:ℕ) (v a b:ℝ) : Prop where
   log i : i∈Set.Icc a b → Brush K v 1 Real.log i
   secant x : x∈Set.Icc a b ×ˢ Set.Icc a b → Brush K v 1 sec x
lemma treasury (k:ℕ)(a b:ℝ)(ha:0<a):∃ u>0,Treasury k u a b:=by
   let S:=Set.Icc a b; obtain ⟨v,hv,hV⟩:= Brush.compact (k:=k) (f:=Real.log) (isCompact_Icc (a:=a) (b:=b)) fun x hx=> Real.contDiffAt_log.mpr (ha.trans_le hx.1).ne'
   obtain ⟨c,hc,H⟩:= Brush.compact (k:=k) (s:= S ×ˢ S) (f:=sec) (isCompact_Icc.prod isCompact_Icc) fun x hx=> sec_smooth k x (ha.trans_le hx.1.1) (ha.trans_le hx.2.1)
   exact ⟨max c v, hc.trans_le (le_max_left ..),fun i hi=> (hV i hi).climb (le_max_right ..) le_rfl,fun i hi=> (H i hi).climb (le_max_left ..) le_rfl⟩

-- prices including normalizing. Let `w` be u radius (≥ t in terminal);
-- multiplication cost convert since if kept 2/w you'd have to rewire all support.
omit [FiniteDimensional ℝ E]
private lemma move_norm {q w : ℝ}{x:E}(h:Brush n q (w+w) f x)(hw:0 ≤ w): Brush n (2^n*q) w f x := by
   refine ⟨h.smooth,hw,fun i hi=>?_⟩; refine (h.order i hi).trans ?_; rw [← two_mul, mul_pow, ← mul_assoc]; refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hw _); rw [mul_comm _ (2^i)]; exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two hi) h.nonneg

def peg (n : ℕ) (D C b v:ℝ) := (2:ℝ)^n*(D* Lantern.clump n (2*(C+b)) v)

lemma log_variation (h: Treasury n v a b) {W U:ℝ}(ha:0<a)(hF:Brush n W 1 f x)(hR:Brush n U 1 r x)
    (hf:f x∈ Set.Icc a b)(hu:r x∈Set.Icc a b)(hw:1 ≤ C)(hp:Brush n D C (f-r) x):
   Brush n (peg n D W U v) C (fun x => Real.log (f x)-Real.log (r x)) x:= by
  have hz:0<f x:=ha.trans_le hf.1; have ht:0< r x:=ha.trans_le hu.1
  have he : Brush n (2*(W+U)) 1 (fun x=> (r x, f x)) x:=  by rw [two_mul]; exact (hR.climb (le_add_of_nonneg_left hF.nonneg) le_rfl).pair (hF.climb (le_add_of_nonneg_right hR.nonneg) le_rfl)
  let u:=fun x=> sec (r x, f x); let V:= Lantern.clump n (2*(W+U)) v
  have hv : Brush n V C u x:= (Lantern.composite he (h.secant _ ⟨hu,hf⟩)).climb le_rfl hw
  refine ((move_norm (hp.paints hv) (zero_le_one.trans hw))).shimmy ?_
  filter_upwards [hF.smooth.continuousAt.eventually (lt_mem_nhds hz), hR.smooth.continuousAt.eventually (lt_mem_nhds ht)] with y hy hx; exact secant (r y) (f y) hx hy
end YM.Juniper.LocalAtlas
