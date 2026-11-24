import YM.Trace.ActualSpectral
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
Forward spectral model with normalization from its rest Laplace value. Used
as limiting positive measure, not substituted for the physical spectral measure. Full
spacetime coordinates use Euclidean Lebesgue measure in the radian convention.
-/
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
namespace YM.Trace
open Mink Boundary Set Filter Function MeasureTheory Real
open scoped Topology BigOperators Matrix.Norms.Frobenius InnerProductSpace ENNReal Pointwise

def targetNorm (A : ℝ) := A/(1536 * Real.pi)
lemma targetNorm_nonneg {A : ℝ} (h : 0≤A) : 0 ≤ targetNorm A := by unfold targetNorm; have := Real.pi_pos; positivity
lemma targetNorm_pos {A : ℝ} (h : 0<A) : 0 < targetNorm A := by unfold targetNorm; have := Real.pi_pos; positivity
noncomputable def modelWeight (x : E4) := cone.indicator (fun p:E4 => (Mink.m p)^2) x
lemma modelWeight_nonneg (x : E4) : 0 ≤ modelWeight x := by by_cases h : x∈cone <;> simp [modelWeight,h]; positivity
lemma modelWeight_le (x : E4) : modelWeight x ≤ ‖x‖^4 := by
  by_cases h : x∈cone
  · have ht := Mink.squares x
    simp only [modelWeight,indicator_of_mem h,Mink.m]; nth_rw 1 [show ‖x‖^4=(‖x‖^2)^2 from by ring]; rw [ht]; nlinarith [sq_nonneg (time x),sq_nonneg ‖spatial x‖]
  simp only [modelWeight,indicator_of_notMem h]; positivity
@[fun_prop] lemma measurable_modelWeight : Measurable modelWeight := by unfold modelWeight; apply Measurable.indicator ?_ closed_cone.measurableSet; fun_prop
lemma modelWeight_move (g : Lorentz) (x : E4) : modelWeight (g.act x)=modelWeight x := by by_cases h : x∈cone <;> simp [modelWeight,h] 

noncomputable def modelDensity (A : ℝ) (x : E4) : ℝ≥0∞ := ENNReal.ofReal (targetNorm A * modelWeight x)
noncomputable def masslessMeasure (A : ℝ) : Measure E4 := volume.withDensity (modelDensity A)
@[fun_prop] lemma modelDensity_meas (A : ℝ) : Measurable (modelDensity A) := by unfold modelDensity; fun_prop
lemma modelDensity_real (A : ℝ) (h : 0≤A) (x) : (modelDensity A x).toReal= targetNorm A * modelWeight x := by
    apply ENNReal.toReal_ofReal; exact mul_nonneg (targetNorm_nonneg h) (modelWeight_nonneg _)
lemma massless_future (A : ℝ) : ∀ᵐ x ∂masslessMeasure A, x ∈ cone := ae_iff.mpr (by
    change volume.withDensity _ (coneᶜ)=_
    rw [withDensity_apply _ closed_cone.measurableSet.compl]; apply (lintegral_eq_zero_iff (f:=modelDensity A) (modelDensity_meas A)).mpr
    filter_upwards [ae_restrict_mem closed_cone.measurableSet.compl] with x hx; simp [modelDensity,modelWeight,show x∉cone from hx])
lemma massless_growth (A : ℝ) : Tempered (masslessMeasure A) := by
    refine ⟨8,|targetNorm A| *(Real.pi^2 / 2),?_⟩
    intro r hr
    let B := Metric.closedBall (0:E4) r
    have he : MeasurableSet B := Metric.isClosed_closedBall.measurableSet
    let k := ENNReal.ofReal (|targetNorm A| *r^4)
    change volume.withDensity _ B ≤ _; rw [withDensity_apply _ he]
    refine (le_trans (b:=∫⁻ p in B, k) (lintegral_mono_ae (((ae_restrict_mem he).mono) (fun p hp=> ?_))) ?_)
    · unfold k modelDensity
      apply ENNReal.ofReal_le_ofReal; exact mul_le_mul (le_abs_self _) ((modelWeight_le p).trans ((pow_le_pow_left₀ (norm_nonneg _) (by simpa [B] using hp : ‖p‖≤r) _)))
          (modelWeight_nonneg _) (abs_nonneg ..)
    unfold k; rw [setLIntegral_const,InnerProductSpace.volume_closedBall_of_dim_even (k:=2) (by simp), show Module.finrank ℝ E4=4 by simp,
        ENNReal.ofReal_mul (abs_nonneg _),ENNReal.ofReal_pow (by linarith : 0≤r),ENNReal.ofReal_mul (abs_nonneg _),
        show (2:ℕ).factorial=2 by decide] 
    push_cast; exact le_of_eq (by rw [show 8=4+4 by norm_num,pow_add]; ac_rfl)
lemma massless_shadow (A : ℝ) : Shadow (masslessMeasure A) := by
   obtain ⟨n,K,hk⟩:=massless_growth A; exact hk.shadow ENNReal.ofReal_lt_top (massless_future _)

variable {A:ℝ}
lemma massless_testing {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (h : 0≤A) (f : E4→E) :
    ∫ p,f p ∂masslessMeasure A = targetNorm A • ∫ p in cone, (Mink.m p)^2 • f p := by
   change ∫ p,f p ∂volume.withDensity _ = _
   rw [integral_withDensity_eq_integral_toReal_smul (modelDensity_meas _) (by unfold modelDensity; simp),
     ← MeasureTheory.integral_indicator (f:=fun x:E4 => (Mink.m x)^2 • f x) closed_cone.measurableSet,
     ← MeasureTheory.integral_smul (targetNorm A)]
   apply integral_congr_ae; filter_upwards with x; rw [modelDensity_real A h,mul_smul]; by_cases hx : x∈cone <;> simp [modelWeight,hx]
lemma massless_invariant (h : 0≤A) (g : Lorentz) (f : E4→ℝ) : ∫ p,f (g.act p)∂masslessMeasure A = ∫ p,f p∂masslessMeasure A := by
   -- no measurability restriction
   have H := g.preserves.integral_comp g.sends.toHomeomorph.measurableEmbedding
      (fun x : E4=> (targetNorm A * modelWeight x) * f x)
   simp only [masslessMeasure, integral_withDensity_eq_integral_toReal_smul (modelDensity_meas _) (by unfold modelDensity; simp)]
   simpa only [modelDensity_real A h,smul_eq_mul,Lorentz.sent,modelWeight_move] using! H
lemma volume_combine : MeasurePreserving (⇑Mink.divide.symm) volume volume :=
   Mink.volume_divide.symm (Mink.divide.toHomeomorph.toMeasurableEquiv)
open YM Boundary -- position etc
private lemma split_moment {s : ℝ} (h : s>0) : let f (T r : ℝ) := Real.exp (-s*T) * (T^2 - r^2)^2;
    let k (T r : ℝ) := if r ≤ T then f T r else 0;
    Integrable (fun p : Space3 × ℝ => k p.2 ‖p.1‖) ∧
    (∫ p:E4, modelWeight p * Real.exp (-s*time p)) = ∫ T:ℝ, ∫ x:Space3, k T ‖x‖ := by
   let f (T r : ℝ) := Real.exp (-s*T) * (T^2 - r^2)^2
   let k (T r : ℝ) := if r ≤ T then f T r else 0
   let J p := modelWeight p * Real.exp (-s*time p)
   let ε := 1536 * Real.pi
   have hN : targetNorm ε=1 := div_self (by have := Real.pi_pos; positivity)
   have hv := (integrable_withDensity_iff (μ:=volume) (modelDensity_meas ε)
         (by unfold modelDensity; simp)).mp (massless_shadow ε|>.energy (p:=s • basis timeAxis) (hp:=by simp [inside,h]))
   simp only [modelDensity_real ε (by unfold ε; positivity),inner_smul_right,inner_time,hN,one_mul,exponential] at hv
   have hJ : Integrable J := hv.congr (ae_of_all _ fun x=> by simp only [J,neg_mul]; rw [mul_comm])
   have he (p:Space3) (T:ℝ) : J (Mink.divide.symm (p,T)) = k T ‖p‖ := by
        unfold J k f; split_ifs with ht <;> simp [modelWeight,cone,m,ht,mul_comm]
   let K (p : Space3 × ℝ) := k p.2 ‖p.1‖
   have HE (p : Space3 × ℝ) := he p.1 p.2
   change (∀ p, J (Mink.divide.symm p)=K p) at HE
   have eQ : (J ∘ ⇑Mink.divide.symm)=K := funext HE
   have ht := volume_combine.integrable_comp_emb (Mink.divide.symm.toHomeomorph.measurableEmbedding) |>.mpr hJ
   rw [eQ] at ht
   refine ⟨ht,?_⟩
   rw [show (∫ p:E4, modelWeight p * Real.exp (-s*time p)) = ∫ p, J p from rfl,
       ← volume_combine.integral_comp Mink.divide.symm.toHomeomorph.measurableEmbedding]
   simp_rw [HE]; exact (MeasureTheory.integral_prod_symm K ht)

lemma volume_three : (volume : Measure Space3).real (Metric.ball 0 1)=Real.pi * 4/3 := by
    have := Real.pi_pos
    simp only [Measure.real,EuclideanSpace.volume_ball_fin_three, ENNReal.ofReal_one,one_pow,one_mul,ENNReal.toReal_ofReal (by positivity : Real.pi * 4 /3 ≥ 0)] -- _?

private lemma radial_poly (s T : ℝ) (hT : T > 0) :
    let f (T r : ℝ) := Real.exp (-s*T) * (T^2 - r^2)^2; let k (T r : ℝ) := if r ≤ T then f T r else 0;
    (∫ x : Space3, k T ‖x‖) = 4*Real.pi * Real.exp (-s*T) * ((8:ℝ)/105 * T^7) := by
    intro f k
    let P (r : ℝ) := r^2*(T^2-r^2)^2
    rw [integral_fun_norm_addHaar volume (k T),volume_three]
    have hE (y:ℝ) : y^(2:ℕ) • (k T y) = (Iic T).indicator (fun r => Real.exp (-s*T) * P r) y := by
        by_cases ht : y ≤ T <;> simp only [Set.indicator,k,P,f,mem_Iic,ht,if_true,if_false,smul_eq_mul,mul_zero] 
        · ring
    simp only [show Module.finrank ℝ Space3 = 3 from by simp] -- nat simplification
    norm_num only [Nat.reduceSub, Nat.cast_ofNat, nsmul_eq_mul, smul_eq_mul]
    rw [show (fun y : ℝ=> y^2 * k T y)=_ from funext hE,setIntegral_indicator measurableSet_Iic,Ioi_inter_Iic,
         MeasureTheory.integral_const_mul,← intervalIntegral.integral_of_le hT.le]
    have Hm n : IntervalIntegrable (fun x:ℝ => x^n) volume 0 T := Continuous.intervalIntegrable (continuous_id'.pow n) _ _
    have eP (x:ℝ) : P x=T^4*x^2+x^6-(2*T^2)*x^4 := by dsimp [P]; ring
    rw [show P=_ from funext eP,intervalIntegral.integral_sub (((Hm _).const_mul _).add (Hm _)) ((Hm _).const_mul _),
       intervalIntegral.integral_add ((Hm _).const_mul _) (Hm _),intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    simp_rw [integral_pow]; norm_num; ring
private lemma radial_fn (s : ℝ) : let f (T r : ℝ) := Real.exp (-s*T) * (T^2 - r^2)^2;
    let k (T r : ℝ) := if r ≤ T then f T r else 0
    ∀ (T : ℝ), (∫ x : Space3, k T ‖x‖) = (Ioi (0:ℝ)).indicator (fun T => (32*Real.pi/105)*(T^7 * Real.exp (-s*T))) T := by
    intro f k T
    by_cases h : T > 0
    · refine (radial_poly s T h).trans ?_; rw [indicator_of_mem (s:=Ioi 0) (f:=(fun T:ℝ=>32 * π / 105 * (T ^ 7 * rexp (-s * T)))) h]; ring
    · rw [indicator_of_notMem (s:=Ioi 0) (f:=(fun T:ℝ=>32 * π / 105 * (T ^ 7 * rexp (-s * T)))) h]; suffices ∀ x : Space3, k T ‖x‖=0 from by simp_rw [this]; simp
      intro x; unfold k; split_ifs with hx
      · have he : ‖x‖=T := by linarith [norm_nonneg x]
        simp [f,he]
      rfl
private lemma moment_inner {s : ℝ} (hs : 0<s) : (∫ T in Ioi (0:ℝ), T^7 * Real.exp (-s*T)) = s⁻¹^8 * 5040 := by
    have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a:=8) (r:=s) (by norm_num) hs
    convert h using 1
    · apply setIntegral_congr_fun measurableSet_Ioi; intro t ht; dsimp only
      rw [show (8:ℝ)-1=((7:ℕ):ℝ) from by norm_num, Real.rpow_natCast, neg_mul]
    · norm_cast; rw [show Real.Gamma 8=5040 from by convert Real.Gamma_nat_eq_factorial 7 using 1 <;> norm_num] 
      simp [one_div]
lemma model_moment (s : ℝ) (h : s>0) : (∫ p:E4, modelWeight p * Real.exp (-s*time p)) = 1536 * Real.pi * s⁻¹^8 := by
    rw [(split_moment h).2]
    simp_rw [radial_fn s]; rw [MeasureTheory.integral_indicator measurableSet_Ioi,MeasureTheory.integral_const_mul,moment_inner h]; ring
lemma model_laplace (hA : A≥0) {x : E4} (hx : x ∈ inside) : (∫ p, exponential p x∂masslessMeasure A) = A / (Mink.m x)^4 := by
   obtain ⟨g,hg⟩ := future_rest x hx
   have hs : 0<Mink.m x := (strict_self _).1 hx |>.2
   let s := √(Mink.m x)
   have h (p : E4) : exponential p x = exponential (g.dual.act p) (s • basis timeAxis) := by
       unfold exponential; rw [← hg,(real_inner_comm x p), (real_inner_comm (g.act x) (g.dual.act p)), g.dual_sent p x] 
   simp_rw [h]
   rw [massless_invariant hA g.dual (fun p => exponential p (s • _))]
   rw [massless_testing hA, ← integral_indicator (f:=fun p=> _) closed_cone.measurableSet]
   have he (p : E4) : ∀ x : E4, (cone.indicator (fun p:E4=>(Mink.m p)^2 • exponential p x)) p = modelWeight p * exponential p x := by
       unfold modelWeight; by_cases hp : p∈cone <;> simp [hp]
   simp_rw [he,exponential,inner_smul_right,inner_time, ← neg_mul]
   rw [model_moment s (Real.sqrt_pos.mpr hs),smul_eq_mul, targetNorm, inv_pow,show s^8=(Mink.m x)^4 by unfold s; rw [show 8=2*4 by norm_num,pow_mul,Real.sq_sqrt hs.le]]
   field_simp [ne_of_gt Real.pi_pos]
variable {G : Gauge} {C : Family G} {S : Table C.book} {f : Extraction.Order}
/-- Exact limit statement reduced to the coincidence rate on the same construction (a
partial implication here, not asserting that rate for an arbitrary `Final`). -/
lemma precise_from_coincidence (Y : Spec.Final C f S) (h : LogLaw Y A) (hA : A>0) : let e:=meanExact Y;
   ∃ M : Measure E4,∃ hm : Tempered M, FieldsNorm M (thetaV Y e) ∧ Thermal M A ∧
          (∀ s>0, restTrace Y e s = (∫ p, Real.exp (-s*time p)∂M : ℝ)) ∧
          (∀ φ : E4→ℂ, Continuous φ→HasCompactSupport φ→ Tendsto (fun r => ∫ p,φ p∂rescaled M r) atTop
                (𝓝 (((targetNorm A : ℝ):ℂ) • ∫ p in Mink.cone, ((Mink.m p)^2 : ℝ) • φ p))) ∧
          (∀ φ : Test4, (∫ k,φ k∂M) = Tickets hm φ ∧ Tendsto (fun r => ∫ p, φ p ∂rescaled M r) atTop (𝓝 (
                ((targetNorm A : ℝ):ℂ) • ∫ p in Mink.cone, ((Mink.m p)^2: ℝ) • φ p))) ∧
          (∀ φ : Joint 2, Tendsto (fun r => logWeight r • spacetimeScaled Y e r φ) atTop (𝓝 (
                ((targetNorm A:ℝ):ℂ) • ∫ p in Mink.cone, ((Mink.m p)^2:ℝ) • relative2 φ p))) := by
   obtain ⟨M,hm,ht,hT,hs,hv,hz,htest⟩ := conditional_distributional Y _ rfl h (masslessMeasure A) (massless_shadow _) (fun _ => model_laplace hA.le) (massless_growth _)
   simp_rw [Tickets_eval (massless_growth _), massless_testing (A:=A) hA.le] at hv hz htest
   exact ⟨M,hm,ht,hT,hs,hv,hz,htest⟩
end YM.Trace
