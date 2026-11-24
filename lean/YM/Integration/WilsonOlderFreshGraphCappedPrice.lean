import YM.Integration.WilsonOlderFreshGraphInvoiceOrder

/-! Price a prebooked narrower strip on the original figure.
Only the derivative count and the smaller width enter the additional cash. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshGraphCappedPrice
open RG Wilson QuadraticLocal.Earn Push.AbsoluteSums Next.Scheduling
open WilsonOlderFreshGraphInvoiceFace

def degree (s power order:ℕ) := 4+(power*order+Wages.grade s power order)
def factor (n:ℕ)(θ:ℝ):=(1-Real.exp (-θ))⁻¹*(θ⁻¹^n*(n.factorial:ℝ)*Real.exp θ)

private def head (G:Gauge)(B:BudgetPoint)(K:ℝ)(s seats:ℕ)(a:ℝ):=
  Real.exp (a*Invoice.tax s seats)*(Footprint.spread 1 (B.B+2):ℝ)*stipend G B K s

private theorem product (G:Gauge)(B:BudgetPoint)(K:ℝ)(s seats:ℕ)(a θ:ℝ):
    Invoice.price B K s seats a θ G = head G B K s seats a*factor (degree s B.power B.order) θ:=by
  rw [group]
  unfold common layers head factor degree span Invoice.memories
  ring

theorem permanent (n:ℕ){θ:ℝ}(pos:0<θ):1≤factor n θ:=by
  have geom:1≤(1-Real.exp (-θ))⁻¹:=(one_le_inv₀ (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith)))).mpr
    (sub_le_self _ (Real.exp_pos _).le)
  have high:=WilsonOlderFreshGraphFactorialTariff.lower pos (Nat.zero_le n)
  exact one_le_mul_of_one_le_of_one_le geom (by simpa using high)

theorem monotone {θ:ℝ}(pos:0<θ)(narrow:θ≤1){n k:ℕ}(h:n≤k):factor n θ≤factor k θ:=by
  have g:0≤(1-Real.exp (-θ))⁻¹:=inv_nonneg.mpr (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))).le
  have roof:1≤θ⁻¹ :=(one_le_inv₀ pos).mpr narrow
  have fact:(n.factorial:ℝ)≤(k.factorial:ℝ):=by exact_mod_cast Nat.factorial_le h
  unfold factor
  gcongr

theorem paid (G:Gauge)(B:BudgetPoint){K a θ θ₀:ℝ}(room:1≤K)(along:0≤a)(old:0<θ)(seats:ℕ)
    {s t:ℕ}(rank:s≤t)(pos:0<θ₀):
    Invoice.price B K s seats a θ₀ G ≤ factor (degree s B.power B.order) θ₀*Invoice.price B K t seats a θ G:=by
  have small:=zero_le_one.trans (permanent (degree s B.power B.order) pos)
  have reserve:=permanent (degree t B.power B.order) old
  have gross:0≤head G B K t seats a:=by
    unfold head
    have stipend₀:=WilsonOlderFreshGraphOrderSalary.begins G B room t
    exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (Nat.cast_nonneg _))
      ((show (0:ℝ)≤2^(span B t) by positivity).trans stipend₀)
  have change: head G B K s seats a ≤ head G B K t seats a:=by
    unfold head
    have tariff:Invoice.tax s seats≤Invoice.tax t seats:=by unfold Invoice.tax;gcongr
    have st₀:0 ≤ stipend G B K s:=(show (0:ℝ)≤2^(span B s) by positivity).trans (WilsonOlderFreshGraphOrderSalary.begins G B room s)
    exact mul_le_mul (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left tariff along)) (Nat.cast_nonneg _))
      (WilsonOlderFreshGraphOrderSalary.monotone G B room rank) st₀ (mul_nonneg (Real.exp_pos _).le (Nat.cast_nonneg _))
  rw [product,product]
  calc
    _=factor (degree s B.power B.order) θ₀*head G B K s seats a:=mul_comm _ _
    _≤_:=mul_le_mul_of_nonneg_left (change.trans (le_mul_of_one_le_right gross reserve)) small

theorem capped (G:Gauge)(B:BudgetPoint){K a θ θ₀ fare:ℝ}(room:1≤K)(along:0≤a)(old:0<θ)(pos:0<θ₀)
    (seats:ℕ){s t:ℕ}(rank:s≤t)(enough:1≤fare)
    (stock:factor (degree s B.power B.order) θ₀≤fare)
    (high:Invoice.price B K t seats a θ G≤(2:ℝ)^t*fare):
    Invoice.price B K s seats a (min θ θ₀) G≤256*((2:ℝ)^t*fare)^3:=by
  let H:=(2:ℝ)^t*fare
  have base:1≤(2:ℝ)^t:=one_le_pow₀ (by norm_num)
  have hf:fare≤H:=le_mul_of_one_le_left (zero_le_one.trans enough) base
  have big:1≤H:=enough.trans hf
  have raw:0≤Invoice.price B K t seats a θ G:=(Invoice.positive B K t room seats old G).le
  by_cases yes:θ≤θ₀
  · rw [min_eq_left yes]
    exact (WilsonOlderFreshGraphInvoiceOrder.controlled G B room along old seats rank).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ raw high _) (by norm_num))
  · rw [min_eq_right (le_of_not_ge yes)]
    calc
      _≤_:=paid G B room along old seats rank pos
      _≤H*H:=mul_le_mul (stock.trans hf) high raw (zero_le_one.trans big)
      _≤256*H^3:=by nlinarith [mul_nonneg (sub_nonneg.mpr big) (sq_nonneg H),pow_nonneg (zero_le_one.trans big) 3]

end YM.Integration.WilsonOlderFreshGraphCappedPrice
end
