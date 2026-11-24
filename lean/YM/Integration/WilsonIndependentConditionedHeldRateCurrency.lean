import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Convert a finite paid wallet at the top into reporter powers for the four
terms of the held comparison. All four coefficients can carry their own sign. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedHeldRateCurrency

private theorem oneTerm {x g:ℝ}{s e:ℕ} (xsmall:|x| ≤ 1) (clock:|x| ≤ 8*g)
    (order:s ≤ e) (c:ℝ):
    c*x^e  ≤  |c| * ((8:ℝ)^s*g^s):=by
  calc
    c*x^e  ≤  |c*x^e|:=le_abs_self _
    _ = |c| * |x|^e:=by rw [abs_mul,abs_pow]
    _  ≤  |c| * (8*g)^s:=mul_le_mul_of_nonneg_left
      ((pow_le_pow_of_le_one (abs_nonneg x) xsmall order).trans
        (pow_le_pow_left₀ (abs_nonneg x) clock s)) (abs_nonneg _)
    _ = _:=by rw [mul_pow]

theorem four {x g B Btop M due:ℝ}{p target interior terminal top:ℕ}
    (balance:B*g^2=1) (Bt₀:0 ≤ Btop) (g₀:0 ≤ g)
    (ratio:Btop ≤ 2*B) (xsmall:|x| ≤ 1) (clock:|x| ≤ 8*g)
    (d₀:0 ≤ due) (M₀:0 ≤ M) (wallet:due ≤ M*Btop^(2*p))
    (hi:target+4*p ≤ interior) (he:target+4*p ≤ terminal) (ht:target+4*p ≤ top)
    (i z l h:ℝ):
    due*(i*x^interior+z*x^terminal+l*x^top+h*x^top)  ≤ 
      (M*(2:ℝ)^(2*p)*8^(target+4*p)*(|i|+|z|+|l|+|h|))*g^target:=by
  let c:=|i|+|z|+|l|+|h|
  have c₀:0 ≤ c:=by dsimp [c];positivity
  have sum:i*x^interior+z*x^terminal+l*x^top+h*x^top  ≤ 
      c*(8^(target+4*p)*g^(target+4*p)):=by
    dsimp [c]
    rw [add_mul,add_mul,add_mul]
    exact add_le_add (add_le_add (add_le_add (oneTerm xsmall clock hi i)
      (oneTerm xsmall clock he z)) (oneTerm xsmall clock ht l)) (oneTerm xsmall clock ht h)
  have cancel:B^(2*p)*g^(4*p)=1:=by
    calc
      _=(B*g^2)^(2*p):=by rw [mul_pow,←pow_mul,show 2*(2*p)=4*p by omega]
      _=1:=by rw [balance,one_pow]
  have money:due  ≤  M*(2*B)^(2*p):=wallet.trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ Bt₀ ratio _) M₀)
  calc
    _  ≤  (M*(2*B)^(2*p))*(c*(8^(target+4*p)*g^(target+4*p))):=
      (mul_le_mul_of_nonneg_left sum d₀).trans (mul_le_mul_of_nonneg_right money (by positivity))
    _ = (M*2^(2*p)*8^(target+4*p)*c)*(B^(2*p)*g^(4*p))*g^target:=by
      rw [mul_pow,pow_add g];ring
    _ = _:=by rw [cancel,mul_one]

end YM.Integration.WilsonIndependentConditionedHeldRateCurrency
