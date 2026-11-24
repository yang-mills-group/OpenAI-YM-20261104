import YM.Integration.WilsonCoherentMayerRootTariff

/-! Dependence of the rooted angular coefficient price on its paid strip width. -/
set_option autoImplicit false
set_option maxRecDepth 4096
noncomputable section
open scoped BigOperators
namespace YM.Integration.WilsonCoherentMayerRootGrowth
open AnalyticNext.QuarticMatch.Estimate
open AnalyticNext.QuarticMatch.Estimate.Logfee AnalyticNext.QuarticMatch.Estimate.Plaque
open Lattice WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonCoherentMayerRootTariff

private theorem toll (G:Gauge) (j:ℕ) {t η:ℝ} (ht:0<t) (t1:t≤1) (he:0<η) (e1:η≤1):
    tollBound G (t*η) j=tollBound G η j*(t⁻¹)^j:=by
  have a:1≤η⁻¹:=(one_le_inv₀ he).2 e1
  have b:1≤(t*η)⁻¹:=(one_le_inv₀ (mul_pos ht he)).2 ((mul_le_of_le_one_left he.le t1).trans e1)
  unfold tollBound
  rw [max_eq_right b,max_eq_right a,mul_inv]
  simp only [mul_pow];ring

private theorem planCost (G:Gauge) (j:ℕ) {t η:ℝ} (t1:t≤1) (he:0≤η):
    plan4 G (t*η) j≤plan4 G η j:=by
  unfold plan4
  have h:=Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (mul_le_of_le_one_left he t1) (show (0:ℝ)≤4 by norm_num))
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by have:0≤(unitPrice G j).C:=zero_le_one.trans (unitPrice G j).used;positivity)
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h (by norm_num))
      (zero_le_one.trans (unitPrice G j).used)) j) (ample_pos G).le

private theorem mail (G:Gauge) (j:ℕ) {t η:ℝ} (ht:0<t) (t1:t≤1) (he:0<η) (e1:η≤1):
    mailCharge G (t*η) j=mailCharge G η j*(t⁻¹)^(j*2):=by
  simp only [mailCharge,toll G j ht t1 he e1,pow_mul]
  ring

private theorem total (G:Gauge) (j:ℕ) {t η:ℝ} (ht:0<t) (t1:t≤1) (he:0<η) (e1:η≤1):
    gratuity G (t*η) j≤gratuity G η j*(t⁻¹)^(j*2):=by
  have giftCost:gift G (t*η) j≤gift G η j:=max_le_max_left _ (planCost G j t1 he.le)
  unfold gratuity
  rw [mail G j ht t1 he e1]
  calc
    _≤_ * gift G η j:=mul_le_mul_of_nonneg_left giftCost (mul_nonneg (mailCharge_pos _ _ _).le (pow_nonneg (inv_nonneg.mpr ht.le) _))
    _=_:=by ring

private theorem flour (G:Gauge) (h j:ℕ) {t s:ℝ} (ht:0<t) (t1:t≤1) (hs:0<s) (s1:s≤1):
    Near.flour G (t*s) h j≤Near.flour G s h j*(t⁻¹)^((j*2)*h):=by
  have dp:0<down s j:=div_pos hs (by positivity)
  have d1:down s j≤1:=(div_le_one (by positivity)).2 (s1.trans (by linarith [show (0:ℝ)≤(j:ℝ) by positivity]))
  have dr:down (t*s) j=t*down s j:=by unfold down;ring
  have orig:=total G j ht t1 dp d1
  simp only [Near.flour,dr]
  calc
    _≤(j.factorial:ℝ)⁻¹*((2:ℝ)^j*(gratuity G (down s j) j*(t⁻¹)^(j*2)))^h:=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg (by positivity) (gratuity_pos _ _ _).le)
        (mul_le_mul_of_nonneg_left orig (by positivity)) _) (by positivity)
    _=_:=by simp only [mul_pow,pow_mul];ring

private theorem board (G:Gauge) {t s:ℝ} (ht:0<t) (t1:t≤1) (hs:0<s):
    boardPay (Hooks G) (t*s)≤boardPay (Hooks G) s*(t⁻¹)^(Fintype.card Axis):=by
  have den:0<t*s:=mul_pos ht hs
  have div:(1+t*s)/(t*s)≤((1+s)/s)*t⁻¹:=by
    rw [show ((1+s)/s)*t⁻¹=(1+s)/(t*s) by ring]
    exact div_le_div_of_nonneg_right (by linarith [mul_le_of_le_one_left hs.le t1]) den.le
  unfold boardPay FreeResolvent.sheetPay
  rw [mul_right_comm,←mul_pow,mul_assoc]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left div (by norm_num)) _) (by positivity)

private theorem nonzero (G:Gauge) (h j:ℕ) (z:j≠0) {t:ℝ} (ht:0<t) (t1:t≤1):
    Near.flour G (t/2) h j*(boardPay (Hooks G) ((t/2)/(j:ℝ)))^j≤
      (Near.flour G (1/2) h j*(boardPay (Hooks G) ((1/2)/(j:ℝ)))^j)*(t⁻¹)^((j*2)*h+(Fintype.card Axis)*j):=by
  have f:=flour G h j ht t1 (show (0:ℝ)<1/2 by norm_num) (show (1:ℝ)/2≤1 by norm_num)
  have b:=board G ht t1 (show (0:ℝ)<(1/2)/(j:ℝ) by exact div_pos (by norm_num) (by exact_mod_cast Nat.pos_of_ne_zero z))
  rw [show t*(1/2:ℝ)=t/2 by ring] at f
  rw [show t*((1/2:ℝ)/(j:ℝ))=(t/2)/(j:ℝ) by ring] at b
  calc
    _≤(Near.flour G (1/2) h j*(t⁻¹)^((j*2)*h))*
       (boardPay (Hooks G) ((1/2)/(j:ℝ))*(t⁻¹)^Fintype.card Axis)^j:=
      mul_le_mul f (pow_le_pow_left₀ (boardPay_nn (div_pos (by positivity) (by exact_mod_cast Nat.pos_of_ne_zero z))) b _)
        (pow_nonneg (boardPay_nn (div_pos (by positivity) (by exact_mod_cast Nat.pos_of_ne_zero z))) _)
        (mul_nonneg (Near.flour_nn _ _ _ _) (pow_nonneg (inv_nonneg.mpr ht.le) _))
    _=_:=by rw [pow_add,pow_mul (t⁻¹) (Fintype.card Axis) j,mul_pow];ring

theorem purchased (G:Gauge) (h j:ℕ) {t:ℝ} (ht:0<t) (t1:t≤1):
    price G t h j≤price G 1 h j*(t⁻¹)^((j*2)*h+(Fintype.card Axis)*j):=by
  cases j with
  | zero=>simpa only [price,mul_one,Nat.zero_mul,Nat.mul_zero,Nat.add_zero,pow_zero] using flour G h 0 ht t1 zero_lt_one le_rfl
  | succ j=>simpa only [price,Nat.cast_succ] using nonzero G h (j+1) (Nat.succ_ne_zero _) ht t1

end YM.Integration.WilsonCoherentMayerRootGrowth
