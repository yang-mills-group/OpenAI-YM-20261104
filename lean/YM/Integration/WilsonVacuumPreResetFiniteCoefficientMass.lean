import YM.Integration.WilsonVacuumPreResetFiniteWindingBudget
import YM.Integration.MSFixedRatioSaddleWick
import YM.Next.RANK.Guard

/-! An all-order, finite polynomial price for the genuine normalized finite
vacuum logarithm. The difference of real shifted weight polynomials retains
the entire old nonquadratic input before the Gaussian average. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetFiniteCoefficientMass
open Function Finset PowerSeries FormalBulk08 FormalBulk08.Orb FormalBulk08.Wick FormalBulk08.Series
open Comparison.RG02 Comparison.RG02.Cumulants Next.Rank PhysicalNext.WeightedGaussianMarginal45C.Issue
open scoped Classical BigOperators

variable {U:Type}
private theorem product {n:ℕ}{A B:ℝ}{f g:PowerSeries (MvPolynomial U ℂ)} (ha:0≤A)
    (hf:∀i≤n,Rise.coin (coeff i f)≤A) (hg:∀i≤n,Rise.coin (coeff i g)≤B) {i:ℕ}(hi:i≤n):
    Rise.coin (coeff i (f*g))≤(n+1)*(A*B):=by
  have hb:0≤B:=(Rise.sign _ _ zero_le_one).trans (hg 0 (Nat.zero_le _))
  rw [coeff_mul]
  calc
    _≤∑v∈antidiagonal i,Rise.coin (coeff v.1 f*coeff v.2 g):=Rise.collect _ zero_le_one _ _
    _≤∑_v∈antidiagonal i,A*B:=by
      apply Finset.sum_le_sum
      intro v hv
      have both:v.1+v.2=i:=by simpa using hv
      apply (Rise.funds _ zero_le_one ..).trans
      exact mul_le_mul (hf _ (by omega)) (hg _ (by omega)) (Rise.sign _ _ zero_le_one) ha
    _≤_:=by
      simpa [nsmul_eq_mul] using mul_le_mul_of_nonneg_right (show (i+1:ℝ)≤n+1 by exact_mod_cast Nat.succ_le_succ hi) (mul_nonneg ha hb)

private theorem powers {n:ℕ} (f g:PowerSeries (MvPolynomial U ℂ)) (A D:ℝ)(ha:0≤A)(hd:0≤D)
    (hf:∀i≤n,Rise.coin (coeff i f)≤A) (hg:∀i≤n,Rise.coin (coeff i g)≤A) (delta:∀i≤n,Rise.coin (coeff i (f-g))≤D)(k:ℕ):
    let C:=(n+1:ℝ)*(1+A)
    (∀i≤n,Rise.coin (coeff i (f^k))≤C^k) ∧ (∀i≤n,Rise.coin (coeff i (f^k-g^k))≤C^k*D):=by
  intro C
  induction k with
  | zero=>
    constructor
    · intro i _;by_cases i=0 <;> simp [*,coeff_one,Rise.coin]
    · simp [hd,Rise.coin]
  | succ k ih=>
    have hc:0≤C:=by unfold C;positivity
    have hk:=pow_nonneg hc k
    constructor
    · intro i hi
      rw [pow_succ]
      apply (product hk ih.1 hf hi).trans
      rw [pow_succ];unfold C
      nlinarith [mul_nonneg (by positivity : 0≤(n+1:ℝ)) hk]
    · intro i hi
      have identity:f^(k+1)-g^(k+1)=f^k*(f-g)+(f^k-g^k)*g:=by ring
      rw [identity,map_add]
      apply (Rise.taller _ zero_le_one ..).trans
      apply (add_le_add (product hk ih.1 delta hi) (product (mul_nonneg hk hd) ih.2 hg hi)).trans
      rw [pow_succ];unfold C;ring_nf;exact le_rfl


/-- Finite polynomial price for exponentiating an entire interacting input.
The changed old action is charged linearly and the other factors may interact. -/
theorem real_weight {n:ℕ}{f g:PowerSeries (MvPolynomial U ℂ)}(one:coeff 0 f=0)(two:coeff 0 g=0)
    (A D:ℝ)(ha:0≤A)(hd:0≤D) (hf:∀i≤n,Rise.coin (coeff i f)≤A)
    (hg:∀i≤n,Rise.coin (coeff i g)≤A)(delta:∀i≤n,Rise.coin (coeff i (f-g))≤D):
    Rise.coin (coeff n (expan f-expan g))≤
      (∑k∈range (n+1),Rise.coin (coeff k (exp (MvPolynomial U ℂ))) * ((n+1:ℝ)*(1+A))^k)*D:=by
  rw [map_sub,expan,expan,Series.subst_coeff one _ n n le_rfl,Series.subst_coeff two _ n n le_rfl,
      ←Finset.sum_sub_distrib,Finset.sum_mul]
  apply (Rise.collect _ zero_le_one _ _).trans (sum_le_sum ?_)
  intro k hk
  rw [←mul_sub,mul_assoc]
  apply (Rise.funds _ zero_le_one ..).trans
  apply mul_le_mul_of_nonneg_left _ (Rise.sign _ _ zero_le_one)
  simpa only [map_sub] using (powers f g A D ha hd hf hg delta k).2 n le_rfl

end YM.Integration.WilsonVacuumPreResetFiniteCoefficientMass
end
