import YM.RGComparison.Core16.Insertions

/-! The leading polynomial of a stored Wilson stencil retains every
coefficient of its original finite polynomial. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.WilsonConditionalTaylorThermalPolynomial
open Function Filter
open scoped Topology Classical BigOperators
variable {ι : Type*}

def degree (m : ι →₀ ℕ) := m.sum (fun _ k => k)

def monomial (m : ι →₀ ℕ) (x : ι → ℂ) := ∏ i ∈ m.support, (x i)^(m i)

def entered (P : MvPolynomial ι ℂ) (w : ℕ) (x : ι → ℂ) :=
  ∑ m ∈ P.support with degree m = w, MvPolynomial.coeff m P * monomial m x

private theorem rescale (m : ι →₀ ℕ) (t : ℂ) (x : ι → ℂ) :
    monomial m (fun i => t * x i) = t ^ degree m * monomial m x := by
  simp only [monomial,mul_pow,Finset.prod_mul_distrib,← Finset.prod_pow_eq_pow_sum,
    degree,Finsupp.sum]

theorem original (P : MvPolynomial ι ℂ) (w : ℕ) (lo : ∀ m∈P.support, w ≤ degree m)
    (f : ℝ → ι → ℂ) (x : ι → ℂ)
    (slope : ∀ i, Tendsto (fun t : ℝ => ((t : ℂ)⁻¹ * f t i)) (𝓝[≠] 0) (𝓝 (x i))) :
    Tendsto (fun t : ℝ => (t : ℂ)⁻¹ ^ w * MvPolynomial.eval (f t) P)
      (𝓝[≠] 0) (𝓝 (entered P w x)) := by
  have small : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[≠] 0) (𝓝 0) :=
    Complex.continuous_ofReal.continuousAt.continuousWithinAt
  have each (m : ι →₀ ℕ) (hm : m∈P.support) :
      Tendsto (fun t : ℝ => (t : ℂ)⁻¹^w * (MvPolynomial.coeff m P * monomial m (f t)))
        (𝓝[≠] 0) (𝓝 (if degree m = w then MvPolynomial.coeff m P * monomial m x else 0)) := by
    have priced := lo m hm
    have one : Tendsto (fun t : ℝ => monomial m (fun i => (t : ℂ)⁻¹ * f t i))
        (𝓝[≠] 0) (𝓝 (monomial m x)) := tendsto_finsetProd _ (fun i _ => (slope i).pow _)
    have eqn : (fun t : ℝ => (t : ℂ)^(degree m-w) *
        (MvPolynomial.coeff m P * monomial m (fun i => (t : ℂ)⁻¹ * f t i))) =ᶠ[𝓝[≠] 0]
      fun t : ℝ => (t : ℂ)⁻¹^w * (MvPolynomial.coeff m P * monomial m (f t)) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      have h : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
      rw [rescale,← Nat.sub_add_cancel priced, pow_add,inv_pow,inv_pow]
      field_simp
      simp only [Nat.add_sub_cancel]
      ring
    apply Filter.Tendsto.congr' eqn
    by_cases he : degree m = w
    · simp only [he,Nat.sub_self,pow_zero,one_mul,if_true]
      exact tendsto_const_nhds.mul one
    have pos : degree m - w ≠ 0 := by omega
    simpa only [if_neg he,zero_pow pos,zero_mul] using
      (small.pow (degree m-w)).mul
        ((tendsto_const_nhds (x:=MvPolynomial.coeff m P)).mul one)
  simpa only [entered,Finset.sum_filter,MvPolynomial.eval_eq,Finset.mul_sum,
    monomial,Finsupp.prod] using tendsto_finsetSum P.support each

end YM.Integration.WilsonConditionalTaylorThermalPolynomial
