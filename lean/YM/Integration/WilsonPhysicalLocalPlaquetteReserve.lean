import YM.Integration.WilsonPhysicalLocalPlaquetteForest
import YM.Extra.MULTISOURCE_BOUNDS.Delays

/-! Scalar area and radius for the original log-squared cover.
The constants depend only on the submitted finite collar multiplicity. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonPhysicalLocalPlaquetteReserve
open Lattice RG Wilson Filter WilsonPhysicalLocalPlaquetteForest
open scoped Topology

def tariff (h:ℕ):ℝ:=(16*(9*(h:ℝ))+225)*(4*(9*h+13)*Fintype.card PlaqAxes)+2*(9*h+13)+1

theorem scalar (h D L:ℕ) {s:ℝ} (hs:1≤ s) (d:(D:ℝ)≤9*h*s^4) (l:(L:ℝ)≤3*s):
    2*(radius D L:ℝ)≤tariff h*s^4 ∧ area D L*s^12≤tariff h*s^20:=by
  let a:ℝ:=9*h+13
  let b:ℝ:=16*(9*(h:ℝ))+225
  have s0:=zero_le_one.trans hs
  have s4:=one_le_pow₀ hs (n:=4)
  have l4:=l.trans (mul_le_mul_of_nonneg_left (le_self_pow₀ hs (by decide:4≠0)) (by norm_num:0≤(3:ℝ)))
  have r:(radius D L:ℝ)≤a*s^4:=by
    dsimp [radius,a];push_cast;nlinarith only [d,l4,s4]
  have rows:(lanes D L:ℝ)≤b*s^4:=by
    dsimp [lanes,b];push_cast;nlinarith only [d,l4,s4]
  have b0:0≤b:=by dsimp [b];positivity
  have a0:0≤a:=by dsimp [a];positivity
  have fee:0≤b*(4*a*Fintype.card PlaqAxes):=by positivity
  have tied:tariff h=b*(4*a*Fintype.card PlaqAxes)+2*a+1:=by rfl
  constructor
  · calc
      _≤(2*a)*s^4:=by linarith only [r]
      _≤_:=mul_le_mul_of_nonneg_right (by rw [tied];linarith only [fee]) (pow_nonneg s0 4)
  · have ar:(lanes D L:ℝ)*(radius D L:ℝ)≤(b*s^4)*(a*s^4):=
      mul_le_mul rows r (Nat.cast_nonneg _) (mul_nonneg b0 (pow_nonneg s0 4))
    calc
      _=((lanes D L:ℝ)*(radius D L:ℝ))*(4*(Fintype.card PlaqAxes:ℝ))*s^12:=by unfold area;ring
      _≤((b*s^4)*(a*s^4))*(4*(Fintype.card PlaqAxes:ℝ))*s^12:=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ar (by positivity)) (pow_nonneg s0 12)
      _=(b*(4*a*Fintype.card PlaqAxes))*s^20:=by ring
      _≤_:=mul_le_mul_of_nonneg_right (by rw [tied];linarith only [a0]) (pow_nonneg s0 20)

theorem small (C:ℝ) (k:ℕ) {ε:ℝ} (he:0<ε):
    ∀ᶠ x:ℝ in atTop,C*(Real.log x)^k*(Real.sqrt x)⁻¹≤ε:=by
  filter_upwards [Extra.Multi.hat_affords (C*2^k/ε) k] with x hx
  have h:(C*2^k/ε)*(Real.log x/2)^k*(Real.sqrt x)⁻¹≤1:=hx
  rw [div_pow] at h
  apply (div_le_one₀ he).mp
  calc
    _=(C*2^k/ε)*(Real.log x ^k/2^k)*(Real.sqrt x)⁻¹:=by field_simp
    _≤1:=h

end YM.Integration.WilsonPhysicalLocalPlaquetteReserve
