import YM.RG06.Bare.Calculus
import Mathlib.RingTheory.PowerSeries.Trunc
/-! Powers and slot divisions in formal polynomials, prior to products in any measure. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG06.Rules
open Function Filter CubicMatch
open scoped Topology ContDiff BigOperators Classical
variable {R S ι : Type*} [CommSemiring R] [CommSemiring S]

def count (w : ι →₀ℕ) := w.sum fun _ n=> n

def residualPol (P:MvPolynomial ι R)(al : R→+*S)(l:ι→S)(t:S)(n:ℕ) : S :=
  ∑ w∈P.support, al (P.coeff w) * w.prod (fun i k=>l i^k) * t^(count w-n)

theorem pull_power (P:MvPolynomial ι R) (al:R→+*S)(l:ι→S)(t:S)(n:ℕ)
    (hp : ∀ w∈P.support,n ≤ count w):
    MvPolynomial.eval₂Hom al (fun i=>l i*t) P = residualPol P al l t n * t^n := by
  rw [MvPolynomial.coe_eval₂Hom,MvPolynomial.eval₂_eq,residualPol, Finset.sum_mul]
  refine Finset.sum_congr rfl fun w hw=>?_
  simp_rw [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  change al (P.coeff w) * (_ * t^(count w)) = _
  rw [mul_assoc _ (t^(count w-n)), ← pow_add, Nat.sub_add_cancel (hp w hw), ← mul_assoc]; rfl

theorem pure_pull (P:MvPolynomial ι R) (al:R→+*S)(l:ι→S)(t:S)(n:ℕ)
    (hp : ∀ w∈P.support,n = count w):
    MvPolynomial.eval₂Hom al (fun i=>l i*t) P = MvPolynomial.eval₂Hom al l P * t^n := by
  rw [pull_power P al l t n (fun w hw=> (hp w hw).le)]
  apply congrArg (· * t^n)
  rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq, residualPol]; exact Finset.sum_congr rfl (fun w hw=>by rw [←hp w hw,Nat.sub_self,pow_zero,mul_one]; rfl)

open PowerSeries
variable {l a : ι→PowerSeries ℂ}{f:ι→ℝ→ℂ}
/-- Independent slot prescription `l`, AFTER division by t. There is a
zero-sector identity for the inputs, not needed as a separate premise since
HasSeries includes its k=0 test. Allows arbitrary distinct, repeated or shared
stochastic tags but says nothing about their probability. -/
theorem divide_rules (P:MvPolynomial ι ℂ)(n:ℕ)(hp:∀ w∈P.support,n≤ count w)(h:∀ i,HasSeries (f i) (l i*X)) :
    HasSeries (fun t=>MvPolynomial.eval (fun i=>f i t) P)
      (residualPol P PowerSeries.C l X n * X^n) := by
  rw [←pull_power P PowerSeries.C l X n hp]; exact HasSeries.subst h P

lemma divide_lower {f:ℝ→ℂ}{a:PowerSeries ℂ}{n:ℕ} (h:HasSeries f (a*X^n)){k:ℕ}(hk:k<n) :
    CubicMatch.term k f=0 := by rw [h.get,coeff_mul_X_pow',if_neg (not_le.mpr hk)]

lemma divide_upper {f:ℝ→ℂ}{a:PowerSeries ℂ}{n:ℕ} (h:HasSeries f (a*X^n))(k:ℕ) :
    CubicMatch.term (k+n) f=coeff k a := by rw [h.get, coeff_mul_X_pow]

/-- Leading bare term after division, at *exactly* the encoded slot grade;
higher monomials can be present when encoding arbitrary SectionData by pop.
-/
theorem residual_lead (P:MvPolynomial ι ℂ)(n:ℕ) (hp:∀ w∈P.support,n≤count w) :
    constantCoeff (residualPol P PowerSeries.C l X n) =
      ∑ w∈P.support with count w=n, P.coeff w * w.prod (fun i k=>constantCoeff (l i)^k) := by
    classical
    rw [Finset.sum_filter,residualPol,_root_.map_sum]
    refine Finset.sum_congr rfl (fun w hw=>?_)
    simp only [Finsupp.prod,map_mul,_root_.map_prod,map_pow,constantCoeff_X,constantCoeff_C]
    split
    next h=> rw [h]; simp
    next h=> rw [zero_pow (n:=count w-n) (by specialize hp w hw; omega),mul_zero]
end YM.RG06.Rules
