import YM.Integration.WilsonPhysicalHistoryRetainedSpringLocalDensity
import Mathlib.Analysis.Complex.Exponential

/-! The finite expansion keeps each signed power of the earlier action
with the correlated test at its original configuration. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.OriginalMarkedRunAction
open Filter Finset MeasureTheory
open scoped Classical BigOperators
variable {X:Type*}[MeasurableSpace X]

def springMomentSum (μ:Measure X)(h:X→ℝ)(n:ℕ)(F:X→ℂ):ℂ:=
  ∑k∈Finset.range n,((k.factorial:ℂ)⁻¹)*(∫u,(h u:ℂ)^k*F u ∂μ)

def springTaylorCost (n:ℕ):ℝ:=(n.succ:ℝ)*((n.factorial:ℝ)*(n:ℝ))⁻¹

theorem spring_moment_sum (μ:Measure X)(h:X→ℝ)(mh:Measurable h){a:ℝ}
    (bound:∀u,|h u|≤a)(small:a≤1)(n:ℕ)(pn:0<n)(F:X→ℂ)(hf:Integrable F μ):
    ‖(∫u,(Real.exp (h u):ℂ)*F u ∂μ)-springMomentSum μ h n F‖≤
      a^n*springTaylorCost n*∫u,‖F u‖ ∂μ:=by
  let term (k:ℕ)(u:X):ℂ:=(h u:ℂ)^k/(k.factorial:ℂ)
  let z (u:X):ℂ:=Real.exp (h u)
  have ub (u:X):‖(h u:ℂ)‖≤1:=by simpa only [Complex.norm_real,Real.norm_eq_abs] using (bound u).trans small
  have power (k:ℕ):Integrable (fun u=>(h u:ℂ)^k*F u) μ:=by
    apply hf.norm.mono' (((Complex.continuous_ofReal.measurable.comp mh).pow_const k).aestronglyMeasurable.mul hf.aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun u=>by
      change ‖(h u:ℂ)^k*F u‖≤‖F u‖
      rw [norm_mul,norm_pow]
      exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) (ub u))
  have t (k:ℕ)(u:X):term k u*F u=(k.factorial:ℂ)⁻¹*((h u:ℂ)^k*F u):=by unfold term;ring
  have tr (k:ℕ):Integrable (fun u=>term k u*F u) μ:=by simp_rw [t];exact (power k).const_mul _
  have sumEq:springMomentSum μ h n F=∫u,∑k∈Finset.range n,term k u*F u ∂μ:=by
    rw [integral_finsetSum _ (fun k _=>tr k)]
    simp_rw [t,integral_const_mul];rfl
  have zi:Integrable (fun u=>z u*F u) μ:=by
    apply (hf.norm.const_mul (Real.exp 1)).mono' ((Complex.continuous_ofReal.measurable.comp (Real.measurable_exp.comp mh)).aestronglyMeasurable.mul hf.aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun u=>by
      change ‖(Real.exp (h u):ℂ)*F u‖≤Real.exp 1*‖F u‖
      rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le]
      exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ((le_abs_self _).trans ((bound u).trans small))) (norm_nonneg _)
  change ‖(∫u,z u*F u ∂μ)-_‖≤_
  rw [sumEq,←integral_sub zi (integrable_finsetSum _ (fun k _=>tr k)),←integral_const_mul]
  apply norm_integral_le_of_norm_le (hf.norm.const_mul _)
  apply Filter.Eventually.of_forall
  intro u
  have polybound:=Complex.exp_bound (ub u) pn
  have own:‖(h u:ℂ)‖^n≤a^n:=by simpa only [Complex.norm_real,Real.norm_eq_abs] using pow_le_pow_left₀ (abs_nonneg _) (bound u) n
  change ‖z u*F u-∑k∈Finset.range n,term k u*F u‖≤_
  rw [←Finset.sum_mul,←sub_mul,norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  change ‖(Real.exp (h u):ℂ)-∑k∈Finset.range n,(h u:ℂ)^k/(k.factorial:ℂ)‖≤_
  rw [Complex.ofReal_exp]
  exact polybound.trans (mul_le_mul_of_nonneg_right own (by positivity))

end YM.Integration.OriginalMarkedRunAction
