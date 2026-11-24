import YM.Trace.ScalarAction
import YM.Trace.Boost
import YM.Trace.ConeValues
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Transfer of a trace logarithmic-precision estimate at rest to timelike momentum
Laplace tests and uniform mass budgets. Euclidean frequency pairing. -/
noncomputable section
set_option autoImplicit false
namespace YM.Trace
open Mink MeasureTheory Real Filter Set Function Analysis Complex
open scoped ENNReal Topology BigOperators NNReal ContDiff InnerProductSpace

def logWeight (R : ℝ) := (R⁻¹)^8 * (Real.log R)^2
lemma positive_weight {r : ℝ} (hr : 1<r) : 0<logWeight r := by unfold logWeight; exact mul_pos (pow_pos (by positivity) _) (pow_pos (Real.log_pos hr) _)

noncomputable def rescaled (M : Measure E4) (R : ℝ) :=
    ENNReal.ofReal (logWeight R) • Measure.map (fun (p:E4) => R⁻¹ • p) M

noncomputable def scaleCLE (R : ℝ) (hr : R≠0) : E4 ≃L[ℝ] E4 := ContinuousLinearEquiv.smulLeft (Units.mk0 R⁻¹ (inv_ne_zero hr))
lemma rescale_integral (M : Measure E4) {r : ℝ} (hr : 1<r) {E : Type*} [NormedAddCommGroup E]
     [NormedSpace ℝ E] (p : E4→E) : (∫ x, p x ∂rescaled M r)= logWeight r • ∫ x,p (r⁻¹ • x) ∂M := by
   rw [rescaled, MeasureTheory.integral_smul_measure .., ENNReal.toReal_ofReal (positive_weight hr).le]
   have ht:= (scaleCLE r (zero_lt_one.trans hr).ne').toHomeomorph.measurableEmbedding.integral_map (μ:=M) p
   change (∫ x,p x ∂Measure.map (r⁻¹ • (id:E4→E4)) M)=_ at ht
   exact congrArg (logWeight r • ·) ht
structure Thermal (M : Measure E4) (A : ℝ) : Prop where
   future : M (coneᶜ)=0
   symmetric (g : Lorentz) : Measure.map g.act M = M
   integrates {s : ℝ} : 0 < s → Integrable (fun p : E4 => Real.exp (-s*time p)) M
   rate : Tendsto (fun R : ℝ => logWeight R * (∫ p, Real.exp (-(R⁻¹)*time p) ∂M)) atTop (𝓝 A)

variable {M : Measure E4} {A : ℝ}
lemma Thermal.cones (h : Thermal M A) {r : ℝ} (hr : 0<r) : ∀ᵐ x ∂rescaled M r, x∈cone := by
   apply ae_iff.mpr
   change rescaled M r coneᶜ=0
   rw [rescaled,Measure.smul_apply,Measure.map_apply (by fun_prop) closed_cone.measurableSet.compl]
   rw [measure_mono_null (t:=coneᶜ) ?_ h.future, smul_zero]
   exact fun p hp hu => hp (by simpa [cone,inv_pos.mpr hr,abs_of_pos hr,norm_smul] using! hu)

lemma Thermal.growth_bound (h : Thermal M A) : ∃ C : ℝ≥0∞, C<⊤ ∧
    ∀ᶠ R in atTop, Growth (rescaled M R) C 8 := by
  have hA : 0≤A := ge_of_tendsto h.rate (Eventually.of_forall (fun _ => mul_nonneg (by unfold logWeight; positivity)
     (integral_nonneg (fun x=>Real.exp_nonneg _))))
  let C := ENNReal.ofReal (A+1)
  refine ⟨C * ENNReal.ofReal (Real.exp 1), ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top, ?_⟩
  obtain ⟨l,hl⟩:= eventually_atTop.mp (h.rate.eventually (gt_mem_nhds (lt_add_one A)))
  filter_upwards [eventually_ge_atTop l,eventually_gt_atTop 1] with R hR hP
  intro s hs
  rw [rescaled,Measure.smul_apply,smul_eq_mul,Measure.map_apply (by fun_prop) Metric.isClosed_closedBall.measurableSet]
  let d := R*s
  have hd : 1<d := hP.trans_le (le_mul_of_one_le_right (zero_lt_one.trans hP).le hs)
  have hd0 : 0<d := zero_lt_one.trans hd
  let z (x : E4) := Real.exp (-(d⁻¹)*time x)
  let Q := ∫ x,z x∂M
  have hB (p : E4) (hp : ‖R⁻¹ • p‖ ≤ s) : -1 ≤ -(d⁻¹)*time p := by
    rw [norm_smul,Real.norm_of_nonneg (by positivity)] at hp
    have ht : time p ≤ ‖p‖ := le_trans (le_abs_self _) (Trace.norm_time p)
    field_simp
    have H : ‖p‖ ≤ s*R := (div_le_iff₀ (show 0<R by linarith)).1 (by simpa only [div_eq_inv_mul] using hp)
    dsimp only [d]; nlinarith [hd0]
  let η := ENNReal.ofReal (Real.exp (-1)); let v := ENNReal.ofReal ∘ z
  calc
    _ ≤ ENNReal.ofReal (logWeight R) * M {x: E4 | η≤v x} := mul_le_mul_of_nonneg_left (measure_mono ?_) zero_le
    _ ≤ ENNReal.ofReal (logWeight R*Q) / η := ?_
    _ ≤ _ := ?_
  · intro p hp; exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp_of_le (hB _ (by simpa using hp)))
  · rw [ENNReal.ofReal_mul (positive_weight hP).le,show ENNReal.ofReal Q=_ from ofReal_integral_eq_lintegral_ofReal
      (h.integrates (s:=d⁻¹) (by positivity)) (ae_of_all _ fun _=>Real.exp_nonneg _)]
    refine (mul_le_mul_of_nonneg_left (meas_ge_le_lintegral_div (f:=v) (μ:=M) (by unfold v z; fun_prop)
        (show η≠0 by unfold η; positivity) (by finiteness : η≠⊤)) zero_le).trans_eq ?_
    rw [div_eq_mul_inv,div_eq_mul_inv,mul_assoc]; rfl
  have hc := hl d ((le_mul_of_one_le_right (zero_lt_one.trans hP).le hs : R≤d).trans' hR)
  change logWeight d*Q<A+1 at hc
  have hq : Q≤(A+1)/logWeight d := (le_div_iff₀ (positive_weight hd)).mpr (by simpa [mul_comm Q] using hc.le)
  have hlR : 0<Real.log R := Real.log_pos hP
  have hls : 0<Real.log d := Real.log_pos hd
  have hi : R ≤ d := by dsimp only [d]; nlinarith
  have ha : Real.log R ≤ Real.log d := Real.log_le_log (zero_lt_one.trans hP) hi
  unfold C η
  have hr0 := zero_lt_one.trans hP
  rw [← ENNReal.ofReal_div_of_pos (Real.exp_pos _), ← ENNReal.ofReal_pow (by linarith : 0≤s), ← ENNReal.ofReal_mul (p:=A+1) (by linarith),
    ← ENNReal.ofReal_mul (p:=((A+1)*Real.exp 1)) (by have := Real.exp_pos 1; positivity)]
  apply ENNReal.ofReal_le_ofReal
  calc (logWeight R * Q / Real.exp (-1)) ≤ logWeight R * ((A+1)/logWeight d) / Real.exp (-1) := (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hq (positive_weight hP).le) (Real.exp_nonneg _))
       _ = (A+1)*Real.exp 1*(s:ℝ)^8*((Real.log R)^2/(Real.log d)^2) := by
           rw [div_eq_mul_inv, ← Real.exp_neg, neg_neg]
           unfold logWeight; unfold d
           field_simp
       _ ≤ _ := mul_le_of_le_one_right (by have := Real.exp_pos 1; positivity)
            ((div_le_one (sq_pos_of_pos hls)).mpr (pow_le_pow_left₀ hlR.le ha _))

lemma Thermal.timelike (h : Thermal M A) (u : E4) (hu : u∈inside) :
    Tendsto (fun R : ℝ => ∫ p, Real.exp (-inner ℝ p u) ∂rescaled M R) atTop (𝓝 (A/(m u)^4)) := by
  obtain ⟨g,hg⟩:=future_rest u hu
  let s := √(m u)
  have hs : 0<s:= Real.sqrt_pos.mpr ((Mink.strict_self _).mp hu).2
  let V (R : ℝ) := ∫ p, Real.exp (-(s/R)*(time p)) ∂M
  have he (R : ℝ) (hr : 1<R) : (∫ p, Real.exp (-inner ℝ p u) ∂rescaled M R) = logWeight R * V R := by
     rw [rescale_integral M hr]
     congr 1
     have hh (x : E4) : inner ℝ (R⁻¹ • x) u=(s/R)*time (g.dual.act x) := by
       rw [real_inner_smul_left,real_inner_comm u x,← g.dual_sent,hg,real_inner_smul_left,
         Mink.pairing,Mink.roll_space,Mink.roll_clock,inner_zero_left]
       unfold s; ring
     simp_rw [hh,← neg_mul]; exact ((show MeasurableEmbedding (⇑g.dual.act) from g.dual.sends.toHomeomorph.measurableEmbedding).integral_map
       (μ:=M) (fun p=>Real.exp (-(s/R)*time p))).symm.trans (by rw [h.symmetric])
  have hy : Tendsto (fun R : ℝ => logWeight (R/s) * V R) atTop (𝓝 A) := by
     have hEq (R : ℝ) : V R = ∫ p, Real.exp (-(R/s)⁻¹*time p) ∂M := by unfold V; simp [inv_div]
     simpa only [hEq,id_eq,comp_apply] using! (h.rate.comp (tendsto_id.atTop_div_const hs))
  have hρ : Tendsto (fun R : ℝ => Real.log R / Real.log (R/s)) atTop (𝓝 1) := by
     have ht := (tendsto_const_nhds (x:=Real.log s)).div_atTop (Real.tendsto_log_atTop.comp (tendsto_id.atTop_div_const hs))
     have := tendsto_const_nhds (x:=(1:ℝ))|>.add ht
     rw [add_zero] at this
     refine this.congr' ?_
     filter_upwards [eventually_gt_atTop s] with w hw
     have hw' : 1 < w/s := (lt_div_iff₀ hs).mpr (by simpa using hw)
     have he := Real.log_div (hs.trans hw).ne' hs.ne'
     dsimp only [Function.comp_apply, id_eq]
     field_simp [(Real.log_pos hw').ne']; linarith
  convert_to Tendsto (fun R : ℝ => ∫ p, Real.exp (-inner ℝ p u) ∂rescaled M R) atTop (𝓝 ((s⁻¹^8 * 1^2)*A)) using 2
  · have H : s^8=(Mink.m u)^4 := by dsimp [s]; rw [show 8=2*4 from rfl,pow_mul,Real.sq_sqrt ((strict_self _|>.mp hu).2.le)]
    simp [one_pow,inv_pow,H,div_eq_mul_inv,mul_comm]
  refine ((((tendsto_const_nhds (x:=s⁻¹)).pow 8).mul (hρ.pow 2)).mul hy).congr' ?_
  filter_upwards [eventually_gt_atTop (max 1 s)] with t ht
  have ht' : 1<t/s := (lt_div_iff₀ hs).mpr (by rw [one_mul]; exact (le_max_right ..).trans_lt ht)
  rw [he t ((le_max_left ..).trans_lt ht)]; unfold logWeight; field_simp [(Real.log_pos ht').ne']
end YM.Trace
