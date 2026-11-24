import YM.Integration.WilsonMovingNormalizedBank
import YM.MSbar.Pulse.Keg

/-! Removing any finite external grade from the *genuine normalized Cacao
output*. The finite Gaussian still uses its own unmarked denominator and
the unchanged covariance. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorNormalizedOrder

open PowerSeries Finset Matrix FormalBulk08.Series MSbar MSbar.Cacao MSbar.Bakery
open WilsonMovingGaussianResponse WilsonMovingNormalizedBank
open scoped BigOperators Classical Matrix

variable {S : Type*} [CommSemiring S]

def drop (q : ℕ) (T : PowerSeries S) : PowerSeries S := PowerSeries.mk (fun j=>coeff (j+q) T)

theorem factor (q : ℕ) (T : PowerSeries S) (lower : ∀ j<q, coeff j T = 0) :
    T = X^q * drop q T := by
  apply PowerSeries.ext
  intro j
  rw [coeff_X_pow_mul']
  by_cases h:q≤j
  · rw [if_pos h,drop,coeff_mk,Nat.sub_add_cancel h]
  · rw [if_neg h,lower j (Nat.lt_of_not_ge h)]

private theorem tick (p : ℕ) (T : PowerSeries ℝ) (g : ℝ) : taste (p+1) (X*T) g=g*taste p T g := by
  change (∑ i ∈ range (p+1+1),g^i*coeff i (X*T)) = g*∑ i ∈ range (p+1),g^i*coeff i T
  rw [Finset.sum_range_succ',PowerSeries.coeff_zero_X_mul,mul_zero,add_zero,mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [PowerSeries.coeff_succ_X_mul,pow_succ]
  ring

theorem ticks (p q : ℕ) (T : PowerSeries ℝ) (g : ℝ) : taste (p+q) (X^q*T) g=g^q*taste p T g := by
  induction q with
  | zero => simp
  | succ q prev =>
    rw [pow_succ',mul_assoc,Nat.add_succ,tick,prev,pow_succ]
    ring

variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (B : Matrix J I ℝ) (x : View J) {Q : Matrix I I ℝ} (positive : Q.PosDef)
    (f T : PowerSeries (MvPolynomial J ℝ)) (origin : Kind f) (p q : ℕ)

include positive origin

/-- Every affordable mixed coefficient is taken on the same measured Gaussian
coordinates; each grade removal repurchases the genuine order of `growP`. -/
theorem full : Through (p+q) (view x (growP f (X^q*T) (B*Q*B.transpose) ((p+q)+1)))
    (X^q * view x (growP f T (B*Q*B.transpose) (p+1))) := by
  induction q with
  | zero => simp [Through]
  | succ q prev =>
    have step := restored B x positive f (X^q*T) origin (p+q)
    have next := shift prev
    intro i hi
    simpa only [pow_succ',mul_assoc,Nat.add_succ] using (step i hi).trans (next i hi)

theorem finite (g : ℝ) :
    taste (p+q) (view x (growP f (X^q*T) (B*Q*B.transpose) ((p+q)+1))) g =
      g^q*taste p (view x (growP f T (B*Q*B.transpose) (p+1))) g := by
  rw [←ticks p q]
  unfold taste
  apply Finset.sum_congr rfl
  intro i hi
  rw [show coeff i (view x (growP f (X^q*T) (B*Q*B.transpose) ((p+q)+1))) =
      coeff i (X^q*view x (growP f T (B*Q*B.transpose) (p+1))) from
      full B x positive f T origin p q i (Nat.lt_succ_iff.mp (mem_range.mp hi))]

end YM.Integration.WilsonConditionalTaylorNormalizedOrder
end

