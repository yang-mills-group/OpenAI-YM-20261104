import YM.Integration.WilsonSeparatedPrefixKineticChart

/-! A measured quadratic equation at the genuine pair of couplings identifies
the coarse-to-fine inverse chart inside a finite composed optical reading. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixKineticEdge
open Finset PowerSeries WilsonCoeffUV.Blue WilsonCoeffUV.Bank
open WilsonReportingAbsoluteInletForecastBooks WilsonSeparatedPrefixKineticTruncation
open private multiply from YM.Integration.WilsonReportingAbsoluteInletForecastBooks
open scoped BigOperators Classical

private theorem norm_one (A:Cost)(one:constantCoeff A=1){x:ℝ}(x0:0 ≤ x)(x1:x ≤ 1)(e:ℕ):
    |value e A x-1| ≤ x*mass e A:=by
  have zero:value 0 A x=1:=by simpa [value,coeff_zero_eq_constantCoeff_apply] using one
  simpa only [zero,zero_add,pow_one] using tail (Nat.zero_le e) A x0 x1

private theorem square (n:ℕ)(H F:Cost)(same:H*F^2=1){x:ℝ}(x0:0 ≤ x)(x1:x ≤ 1):
    |1-value n H x*(value n F x)^2|  ≤  3*x^(n+1)*mass n H*(mass n F)^2:=by
  have a:=multiply n x x0 x1 H (F^2)
  rw [same,one_value] at a
  calc
    _ ≤ |1-value n H x*value n (F^2) x| + |value n H x*value n (F^2) x-value n H x*(value n F x)^2|:=abs_sub_le ..
    _ ≤ x^(n+1)*(mass n H*(mass n F)^2)+mass n H*(2*x^(n+1)*(mass n F)^2):=by
      apply add_le_add
      · exact a.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mass_pow ..) (mass_nonneg ..)) (pow_nonneg x0 _))
      · rw [←mul_sub,abs_mul];exact mul_le_mul (norm n H x0 x1) (powers n 2 F x0 x1) (abs_nonneg _) (mass_nonneg ..)
    _=_:=by ring

def optical (n:ℕ)(M δ x:ℝ):ℝ:=4*(δ+4*x^(n+1)*M+3*x^(n+1)*M*M^2)

theorem ratio {n e:ℕ}(ne:n ≤ e)(H F:Cost)(same:H*F^2=1)(hH:constantCoeff H=1)(hF:constantCoeff F=1)
    {x r δ M:ℝ}(x0:0 ≤ x)(x1:x ≤ 1)(r0:0 ≤ r)(r2:r ≤ 2)(M1:1 ≤ M)
    (hh:mass n H ≤ M)(hf:mass n F ≤ M)(he:mass e H ≤ M)(small:x*M ≤ 1/2)
    (physical:|1-r^2*value e H x| ≤ δ):
    |r-value n F x| ≤ optical n M δ x:=by
  let t:=value n F x
  let J:=value n H x
  have warm:1/2 ≤ J:=by
    have h:|J-1| ≤ 1/2:=(norm_one H hH x0 x1 n).trans ((mul_le_mul_of_nonneg_left hh x0).trans small)
    linarith only [(abs_le.mp h).1]
  have anchor:|t-1| ≤ 1/2:=(norm_one F hF x0 x1 n).trans ((mul_le_mul_of_nonneg_left hf x0).trans small)
  have t0:1/2 ≤ t:=by linarith only [(abs_le.mp anchor).1]
  have a:|1-J*r^2| ≤ δ+4*x^(n+1)*M:=by
    calc
      _ ≤ |1-r^2*value e H x|+|r^2*value e H x-J*r^2|:=abs_sub_le ..
      _ ≤ δ+4*(x^(n+1)*M):=by
        apply add_le_add physical
        rw [mul_comm J,←mul_sub,abs_mul,abs_of_nonneg (sq_nonneg r)]
        exact mul_le_mul (by nlinarith only [sq_nonneg (2-r),mul_nonneg (sub_nonneg.mpr r2) (by linarith:0 ≤ 2+r)]:r^2 ≤ 4) ((tail ne H x0 x1).trans (mul_le_mul_of_nonneg_left he (pow_nonneg x0 _))) (abs_nonneg _) (by norm_num)
      _=_:=by ring
  have b:|1-J*t^2| ≤ 3*x^(n+1)*M*M^2:=by
    exact (square n H F same x0 x1).trans (mul_le_mul (mul_le_mul_of_nonneg_left hh (by positivity)) (pow_le_pow_left₀ (mass_nonneg ..) hf _) (sq_nonneg _) (by positivity))
  have absEq:J*(r+t)*|r-t|=|J*t^2-J*r^2|:=by
    have jpos:0 ≤ J:=by linarith
    rw [←abs_of_nonneg (mul_nonneg jpos (by linarith:0 ≤ r+t)),←abs_mul,abs_sub_comm (J*t^2) (J*r^2)]
    congr 1;ring
  have both:|J*t^2-J*r^2| ≤ δ+4*x^(n+1)*M+3*x^(n+1)*M*M^2:=by
    have tr:=abs_sub_le (J*t^2) 1 (J*r^2)
    rw [abs_sub_comm (J*t^2) 1] at tr;linarith only [tr,a,b]
  have low:1/4 ≤ J*(r+t):=by nlinarith only [mul_nonneg (show 0 ≤ J-1/2 by linarith) (show 0 ≤ r+t by linarith),r0,t0]
  have cost:=(mul_le_mul_of_nonneg_right low (abs_nonneg (r-t))).trans (absEq.le.trans both)
  change |r-t| ≤ 4*(δ+4*x^(n+1)*M+3*x^(n+1)*M*M^2);linarith

def fare (n:ℕ)(M δ x:ℝ):ℝ:=x*(x^(n+1)*((n:ℝ)+2)*M^(n+1)*M+optical n M δ x*((n:ℝ)+1)*2^n*M)

theorem chronological {n e:ℕ}(ne:n ≤ e)(H F A:Cost)(same:H*F^2=1)(hH:constantCoeff H=1)(hF:constantCoeff F=1)
    {x r δ M:ℝ}(x0:0 ≤ x)(x1:x ≤ 1)(r0:0 ≤ r)(r2:r ≤ 2)(M1:1 ≤ M)
    (hh:mass n H ≤ M)(hf:mass n F ≤ M)(he:mass e H ≤ M)(ha:mass n A ≤ M)(small:x*M ≤ 1/2)
    (physical:|1-r^2*value e H x| ≤ δ):
    |x*value n (chartB A F) x-(x*r)*value n A (x*r)| ≤ fare n M δ x:=by
  let t:=value n F x
  have price:=ratio ne H F same hH hF x0 x1 r0 r2 M1 hh hf he small physical
  have near:|t-1| ≤ 1/2:=(norm_one F hF x0 x1 n).trans ((mul_le_mul_of_nonneg_left hf x0).trans small)
  have tab:max |t| |r| ≤ 2:=by
    apply max_le; · apply abs_le.mpr;constructor <;> linarith [(abs_le.mp near).1,(abs_le.mp near).2]
    rw [abs_of_nonneg r0];exact r2
  have fee:=WilsonSeparatedPrefixKineticChart.cost n A F x0 x1
  have stable:=WilsonSeparatedPrefixKineticChart.stable n A x0 x1 (by norm_num:1 ≤ (2:ℝ)) tab
  rw [abs_sub_comm t r] at stable
  rw [mul_assoc x r,←mul_sub,abs_mul,abs_of_nonneg x0];apply mul_le_mul_of_nonneg_left _ x0
  change |value n (chartB A F) x-WilsonSeparatedPrefixKineticChart.measured n A x r| ≤ _
  refine (abs_sub_le _ (WilsonSeparatedPrefixKineticChart.measured n A x t) _).trans (add_le_add ?_ ?_)
  · refine fee.trans (mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (max_le M1 hf) _) (by positivity)) ha (mass_nonneg ..) (by positivity))
  · refine stable.trans (mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right price (by positivity)) (by positivity)) ha (mass_nonneg ..) ?_)
    exact mul_nonneg (mul_nonneg ((abs_nonneg _).trans price) (by positivity)) (by positivity)

end YM.Integration.WilsonSeparatedPrefixKineticEdge
end
