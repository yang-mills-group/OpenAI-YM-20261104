import YM.SchemeRG11.MSDetector.Direct
/-!
Uniform payment for any spanning equal-helicity line. Critical to apply
PRECISELY at four. Do not infer cancellation of diagrams that still
have poles elsewhere. Used after subtraction/dressing.
-/
set_option autoImplicit false
set_option maxHeartbeats 290000
noncomputable section
namespace YM.SchemeRG11.MSDetector
open Hot Maxwell Analysis Set MeasureTheory Metric Function Filter TopologicalSpace Cluster Steam MSbar Pert Triangle Storm Flare Asymptotics
open scoped Topology ContDiff BigOperators Real RealInnerProductSpace
variable (i j : Eye) {μ : ℝ}
private lemma deal {x:E4}{R : ℝ}(hr:0<R) (hx:x≠0) :
    (∫ t in Ioc 0 R, ∑ a,Steam.tint [a,a] t x)=gauze R x := by
  have hi: IntegrableOn (fun t=>∑ a,Steam.tint [a,a] t x) (Ioi 0):= integrable_finsetSum _ (fun i _=> tint_i [i,i] hx)
  have hp : (∫ t in Ioi 0,∑ a,Steam.tint [a,a] t x)=0:= by
     rw [integral_finsetSum _ (fun i _=> show IntegrableOn (fun t=> Steam.tint [i,i] t x) (Ioi 0) volume from tint_i [i,i] hx)]; exact (Finset.sum_congr (s₁:=(Finset.univ:Finset Axis)) rfl fun a _=> sculpt [a,a] x hx).trans (Maxwell.harmonic hx)
  have hv : Tendsto (fun t=> gauze t x) atTop (𝓝 0):= by
    have hh: Tendsto (fun t:ℝ=> t⁻¹^2) atTop (𝓝 0):= by simpa using (tendsto_inv_atTop_zero (𝕜:=ℝ)).pow 2
    have hg := (Real.continuous_exp.continuousAt (x:=-(4:ℝ)⁻¹*0*‖x‖^2)).tendsto.comp ((tendsto_inv_atTop_zero.const_mul (-(4:ℝ)⁻¹)).mul_const (‖x‖^2))
    have hT:= (hh.const_mul base).mul hg; rw [mul_zero,zero_mul] at hT
    simpa only [comp_def, inv_pow, Steam.α, mul_zero, Real.exp_zero, mul_one,zero_mul,gauze, mul_inv_rev,mul_comm _ (4:ℝ)⁻¹, neg_mul] using hT
  have hT:=integral_Ioi_of_hasDerivAt_of_tendsto' (a:=R) (fun r hh=> stave x (lt_of_lt_of_le hr hh)) (hi.mono_set (Ioi_subset_Ioi hr.le)) hv
  simp only [zero_sub] at hT
  rw [show Ioi (0:ℝ)= Ioc 0 R ∪ Ioi R by rw [Ioc_union_Ioi (le_max_right ..),min_eq_left hr.le], setIntegral_union (t:=Ioi R) (disjoint_left.mpr fun i hi h => not_le_of_gt (show R < i from h) hi.2) measurableSet_Ioi (hi.mono_set Ioc_subset_Ioi_self) (hi.mono_set (Ioi_subset_Ioi hr.le)), hT] at hp
  linarith

lemma chill {x:E4}{R : ℝ}(hx:x≠0)(hr : 0<R) :
    (∫ t in Ioc 0 R,fused false i false j t x)= if i=j then -(2:ℝ)⁻¹*gauze R x else 0 := by
   by_cases he:i=j <;> simp only [dusk,he,↓reduceIte, integral_neg, integral_const_mul]
   · rw [deal hr hx]; ring
   simp

private lemma low_c {t : ℝ} (ht : 0<t) (x:E4) : ‖gauze t x‖ ≤ base*t⁻¹^2 := by
  unfold gauze; have h : 0<base:=by unfold base; positivity
  have hb : 0<Steam.α t:=by unfold Steam.α; positivity
  rw [norm_mul,Real.norm_of_nonneg (by positivity : 0 ≤ base*(t^2)⁻¹),Real.norm_of_nonneg (Real.exp_pos _).le,inv_pow]
  apply mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.mpr ?_)
  rw [neg_mul]; exact neg_nonpos.mpr (by positivity)

lemma poleward : ∃ D>0, ∀ R : ℝ, 1≤R → ∀ x:E4,x≠0 →
   ‖peer μ R (false,i) (false,j) x‖ ≤ D*R⁻¹^2 := by
  have h : 0<base:=by unfold base; positivity
  let c:= base*(2:ℝ)⁻¹
  let f(k:Bins):= ‖weight k‖*c*(times k)⁻¹^2
  have hh k:0≤f k:= by unfold f c; positivity
  let s:= ∑ i,f i
  refine ⟨1+s, by linarith [show 0 ≤ s from Finset.sum_nonneg fun i _=>hh i],fun R hr x hx=>?_⟩
  rw [peer_paid R _ _ hx]; apply (norm_sum_le ..).trans
  apply le_trans ?_ (mul_le_mul_of_nonneg_right (show s≤1+s by linarith) (sq_nonneg _))
  rw [show s=∑ i,f i from rfl,Finset.sum_mul]
  apply Finset.sum_le_sum; intro k _
  have hp: 0<peak R k:= lt_of_lt_of_le zero_lt_one (peak_ge k hr)
  rw [norm_smul,Complex.norm_real,chill i j hx hp]
  split
  · rw [norm_mul, norm_neg,Real.norm_of_nonneg (by positivity : 0≤(2:ℝ)⁻¹)]
    grw [low_c hp x]; unfold f c peak; exact le_of_eq (by ring)
  simp only [norm_zero,mul_zero]; exact mul_nonneg (hh k) (sq_nonneg _)

variable {ι : Type} {v : Filter ι} {R : ι→ℝ} (H : Tendsto R v atTop) {x : ι→E4} (h : ∀ᶠ y in v,x y≠0)
include H h
lemma cohere : (fun y=>peer μ (R y) (false,i) (false,j) (x y))=O[v] (fun y=> (R y)⁻¹^2) := by
  obtain ⟨D,hD,d⟩:= poleward (μ:=μ) i j
  refine IsBigO.of_bound D ((h.and (H.eventually (eventually_ge_atTop 1))).mono fun y hy=> ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _)]; exact d _ hy.2 _ hy.1
end YM.SchemeRG11.MSDetector
