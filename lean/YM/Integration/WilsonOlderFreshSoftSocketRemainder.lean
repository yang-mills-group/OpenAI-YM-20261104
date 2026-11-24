import YM.Integration.WilsonSeparatedPrefixKineticTruncation

/-! Restore the genuine pole on a finite printed socket. The unmarked kinetic correction is submitted as one previously booked series at the real endpoints. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftSocketRemainder
open Finset PowerSeries WilsonCoeffUV.Blue WilsonReportingAbsoluteInletForecastBooks
open WilsonSeparatedPrefixKineticTruncation 
open private multiply from YM.Integration.WilsonReportingAbsoluteInletForecastBooks
open scoped Classical BigOperators

theorem shift (h t:ℕ)(P:Cost)(x:ℝ):value (h+t) (X^h*P) x=x^h*value t P x:=by
  unfold value
  rw [show h+t+1=h+(t+1) by omega,Finset.sum_range_add]
  have zero:∑i∈range h,x^i*coeff i (X^h*P)=0:=by
    apply sum_eq_zero
    intro i hi
    simp only [coeff_X_pow_mul',if_neg (Nat.not_le.mpr (mem_range.mp hi)),mul_zero]
  rw [zero,zero_add,mul_sum]
  apply sum_congr rfl
  intro i _
  simp [coeff_X_pow_mul',pow_add,mul_assoc]

theorem crop {p h:ℕ}(kept:h≤p)(A P:Cost){x:ℝ}(x0:0≤x)(x1:x≤1):
    |value p (X^h*(A^h*P)) x-x^h*(value p A x)^h*value p P x|≤
      x^(p+1)*((h:ℝ)+2)*(mass p A)^h*mass p P:=by
  obtain ⟨t,rfl⟩:=Nat.exists_eq_add_of_le kept
  let n:=h+t
  let B:=(mass n A)^h
  let C:=mass n P
  have B0:0≤B:=pow_nonneg (mass_nonneg ..) _
  have C0:0≤C:=mass_nonneg ..
  have tp:t≤n:=Nat.le_add_left _ _
  have xsmall:=pow_le_pow_of_le_one x0 x1 (Nat.succ_le_succ tp)
  have tar:mass n (A^h*P)≤B*C:=(mass_mul ..).trans (mul_le_mul_of_nonneg_right (mass_pow ..) C0)
  have one:|value t (A^h*P) x-value n (A^h*P) x|≤x^(t+1)*(B*C):=by
    rw [abs_sub_comm]
    exact (tail tp _ x0 x1).trans (mul_le_mul_of_nonneg_left tar (pow_nonneg x0 _))
  have two:|value n (A^h*P) x-value n (A^h) x*value n P x|≤x^(t+1)*(B*C):=by
    exact (multiply n x x0 x1 ..).trans
      (mul_le_mul xsmall (mul_le_mul_of_nonneg_right (mass_pow ..) C0)
        (mul_nonneg (mass_nonneg ..) C0) (pow_nonneg x0 _))
  have three:|value n (A^h) x*value n P x-(value n A x)^h*value n P x|≤
      (h:ℝ)*x^(t+1)*B*C:=by
    rw [←sub_mul,abs_mul]
    refine (mul_le_mul (powers n h A x0 x1) (WilsonSeparatedPrefixKineticTruncation.norm n P x0 x1) (abs_nonneg _) ?_).trans ?_
    · exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg x0 _)) B0
    · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left xsmall (Nat.cast_nonneg _)) B0) C0
  have fare:|value t (A^h*P) x-(value n A x)^h*value n P x|≤
      x^(t+1)*((h:ℝ)+2)*B*C:=by
    calc
      _≤|value t (A^h*P) x-value n (A^h*P) x|+
        (|value n (A^h*P) x-value n (A^h) x*value n P x|+
          |value n (A^h) x*value n P x-(value n A x)^h*value n P x|):=
        (abs_sub_le ..).trans (add_le_add (le_refl _) (abs_sub_le ..))
      _≤_:=by nlinarith only [one,two,three]
  rw [shift,mul_assoc (x^h),←mul_sub,abs_mul,abs_of_nonneg (pow_nonneg x0 _)]
  calc
    _≤x^h*(x^(t+1)*((h:ℝ)+2)*B*C):=mul_le_mul_of_nonneg_left fare (pow_nonneg x0 _)
    _=_:=by dsimp only [B,C,n];rw [show h+t+1=h+(t+1) by omega,pow_add];ring

theorem original {p h:ℕ}(kept:h≤p)(A P:Cost){g x:ℝ}(g0:0<g)(x0:0≤x)(x1:x≤1):
    |(g^h)⁻¹*value p (X^h*(A^h*P)) x-value p P x|≤(g^h)⁻¹*
      (x^(p+1)*((h:ℝ)+2)*(mass p A)^h+|(x*value p A x)^h-g^h|)*mass p P:=by
  let a:=x^h*(value p A x)^h
  let l:=(g^h)⁻¹
  have pay:l*g^h=1:=inv_mul_cancel₀ (pow_ne_zero _ g0.ne')
  have l0:0≤l:=inv_nonneg.mpr (pow_nonneg g0.le _)
  have split:l*value p (X^h*(A^h*P)) x-value p P x =
      l*(value p (X^h*(A^h*P)) x-a*value p P x)+l*((a-g^h)*value p P x):=by
    linear_combination (value p P x)*pay
  change |l*value p (X^h*(A^h*P)) x-value p P x|≤_
  rw [split]
  calc
    _ ≤ |l*(value p (X^h*(A^h*P)) x-a*value p P x)|+|l*((a-g^h)*value p P x)|:=abs_add_le ..
    _ ≤ l*(x^(p+1)*((h:ℝ)+2)*(mass p A)^h*mass p P)+l*(|a-g^h| *mass p P):=by
      simpa only [abs_mul,abs_of_nonneg l0] using add_le_add
        (mul_le_mul_of_nonneg_left (crop kept A P x0 x1) l0)
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (WilsonSeparatedPrefixKineticTruncation.norm p P x0 x1) (abs_nonneg (a-g^h))) l0)
    _ = _:=by dsimp only [a,l];rw [mul_pow];ring

end YM.Integration.WilsonOlderFreshSoftSocketRemainder
end
