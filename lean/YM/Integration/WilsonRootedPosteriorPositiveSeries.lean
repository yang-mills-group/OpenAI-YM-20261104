import YM.Integration.WilsonPhysicalHistoryRetainedSpringLocalTaylor

/-! The finite exponential of the true bounded local discrepancy is a positive
weight at every finite order. The real density is shared by all signed moments. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedPosteriorPositiveSeries
open Filter Finset MeasureTheory RG OriginalMarkedRunAction
open scoped BigOperators Classical
variable {X:Type*}[MeasurableSpace X]

def weight (n:ℕ)(s:ℝ):ℝ:=∑k∈range n,s^k/(k.factorial:ℝ)

theorem positive (n:ℕ)(s:ℝ)(hs:|s|≤1/2):0≤weight n s:=by
  cases n with
  | zero=>simp [weight]
  | succ n=>
    suffices (1/2:ℝ)^n≤weight (n+1) s from (by positivity : 0≤(1/2:ℝ)^n).trans this
    induction n with
    | zero=>simp [weight]
    | succ n ih=>
      have face:(1:ℝ)≤(n+1).factorial:=by exact_mod_cast Nat.factorial_pos (n+1)
      have own:|s^(n+1)/((n+1).factorial:ℝ)|≤(1/2:ℝ)^(n+1):=by
        rw [abs_div,abs_pow,abs_of_pos (lt_of_lt_of_le zero_lt_one face)]
        exact (div_le_self (pow_nonneg (abs_nonneg _) _) face).trans (pow_le_pow_left₀ (abs_nonneg _) hs _)
      have step:=neg_abs_le (s^(n+1)/((n+1).factorial:ℝ))
      change (1/2:ℝ)^(n+1)≤∑k∈range ((n+1)+1),s^k/(k.factorial:ℝ)
      rw [sum_range_succ]
      change (1/2:ℝ)^(n+1)≤weight (n+1) s+_
      linarith [show (1/2:ℝ)^(n+1)=(1/2:ℝ)^n/2 by rw [pow_succ];ring]

theorem moment (μ:Measure X)(h:X→ℝ)(mh:Measurable h)(cap:∀x,|h x|≤1/2)
    (n:ℕ)(f:X→ℂ)(hf:Integrable f μ):
    Integrable (fun x=>(weight n (h x):ℂ)*f x) μ ∧ springMomentSum μ h n f=∫x,(weight n (h x):ℂ)*f x ∂μ:=by
  have hp(k:ℕ):Integrable (fun x=>(h x:ℂ)^k*f x) μ:=by
    apply hf.norm.mono' (((Complex.continuous_ofReal.measurable.comp mh).pow_const k).aestronglyMeasurable.mul hf.aestronglyMeasurable)
    apply Eventually.of_forall
    intro x
    change ‖(h x:ℂ)^k*f x‖≤‖f x‖
    rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (abs_nonneg _) ((cap x).trans (by norm_num)) )
  induction n with
  | zero=>simp [weight,springMomentSum]
  | succ n ih=>
    have place(x:X):(weight (n+1) (h x):ℂ)*f x=(weight n (h x):ℂ)*f x+(n.factorial:ℂ)⁻¹*((h x:ℂ)^n*f x):=by
      simp only [weight,sum_range_succ,Complex.ofReal_add,Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_natCast]
      ring
    have hi:Integrable (fun x=>(n.factorial:ℂ)⁻¹*((h x:ℂ)^n*f x)) μ:=(hp n).const_mul _
    simp_rw [place]
    refine ⟨ih.1.add hi,?_⟩
    rw [integral_add ih.1 hi,integral_const_mul,←ih.2]
    unfold springMomentSum
    rw [sum_range_succ]

theorem bounded (μ:Measure X)[IsProbabilityMeasure μ](h:X→ℝ)(mh:Measurable h)(cap:∀x,|h x|≤1/2)
    (n:ℕ)(f:X→ℂ)(hf:Integrable f μ){b:ℝ}(pos:0≤b)(cost:∀x,‖f x‖≤b):
    ‖springMomentSum μ h n f/springMomentSum μ h n 1‖≤b:=by
  have fy:=moment μ h mh cap n f hf
  have unit:=moment μ h mh cap n 1 (integrable_const (1:ℂ))
  have ei:Integrable (fun x: X=>(weight n (h x):ℂ)) μ:=by simpa only [Pi.one_apply,mul_one] using unit.1
  have ri:Integrable (fun x:X=>weight n (h x)) μ:=by simpa using ei.re
  have j0:0≤∫x,weight n (h x) ∂μ:=integral_nonneg (fun x=>positive n (h x) (cap x))
  have jit:springMomentSum μ h n 1=((∫x,weight n (h x) ∂μ : ℝ):ℂ):=by
    have z:springMomentSum μ h n 1=∫x,(weight n (h x):ℂ) ∂μ:=by simpa only [Pi.one_apply,mul_one] using unit.2
    exact z.trans (integral_complex_ofReal (μ:=μ) (f:=fun x=>weight n (h x)))
  have buy:‖∫x,(weight n (h x):ℂ)*f x ∂μ‖≤(∫x,weight n (h x) ∂μ)*b:=by
    rw [←integral_mul_const]
    apply norm_integral_le_of_norm_le (ri.mul_const b)
    exact Eventually.of_forall fun x=>by
      change ‖(weight n (h x):ℂ)*f x‖≤weight n (h x)*b
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (positive n (h x) (cap x))]
      exact mul_le_mul_of_nonneg_left (cost x) (positive n (h x) (cap x))
  rw [fy.2,jit,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg j0]
  by_cases hz:(∫x,weight n (h x) ∂μ)=0
  · simpa only [hz,div_zero] using pos
  · apply (div_le_iff₀ (lt_of_le_of_ne j0 (Ne.symm hz))).2
    simpa only [mul_comm b] using buy
end YM.Integration.WilsonRootedPosteriorPositiveSeries
