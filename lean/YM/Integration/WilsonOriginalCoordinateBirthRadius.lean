import YM.Integration.WilsonOriginalCoordinateExposure
import YM.Integration.QLocalPhysicalBirthRawRate
import YM.Integration.WilsonLimitConstruction.FundedOriginalRun

/-! The actual source radius for arbitrary Wilson section coordinates, including the
failed-mask bill, on the hierarchy of the existence theorem. -/
set_option autoImplicit false
noncomputable section
universe u

namespace YM.Integration.WilsonOriginalCoordinateBirthRadius
open Finset Filter Lattice Wilson RG Extra.Multi FVA1 PhysicalNext.Repeat
open PhysicalNext.Repeat.Legato WilsonLimitConstruction WilsonOriginalCoordinateExposure
open QLocalPhysicalBirthRawRate
open scoped BigOperators Classical

variable {G : Gauge} (R : Run G)
local notation "A₀" => R.family.path.levels
local notation "β₀" => R.family.path.levels.clock.hatBeta

def overhead := 8 + 4*5^4 * (QLocalPhysicalBirthClock.reserve R)⁻¹

theorem debit (L : ℕ) : (QLocalPhysicalBirthPurchase.debit R L (tolerance R L))⁻¹ ≤
    overhead R * (β₀ L)^8 := by
  let b := β₀ L
  let z := QLocalPhysicalBirthClock.reserve R
  let l := Push.Local.hitWidth ((A₀).budget L)
  have hb : 1 ≤ b := ((A₀).fits.delayed L).le
  have h0 := zero_lt_one.trans_le hb
  have hz : 0 < z := QLocalPhysicalBirthClock.positive R
  have hs : Real.sqrt b ≤ b := by nlinarith [Real.sq_sqrt h0.le,Real.one_le_sqrt.mpr hb]
  have h8 : b ≤ b^8 := by simpa only [pow_one] using pow_le_pow_right₀ (a := b) hb (show 1 ≤ 8 by decide)
  have hwidth : l ≤ 5^4 * b^8 := QLocalPhysicalBirthClock.width A₀ L
  unfold QLocalPhysicalBirthPurchase.debit tolerance
  change (min ((Real.sqrt b)⁻¹/8) (z/(4*l)))⁻¹ ≤ overhead R * b^8
  by_cases h : (Real.sqrt b)⁻¹/8 ≤ z/(4*l)
  · rw [min_eq_left h,inv_div,div_inv_eq_mul]
    have k : 8 ≤ overhead R := le_add_of_nonneg_right (mul_nonneg (by norm_num) (inv_nonneg.mpr hz.le))
    exact mul_le_mul k (hs.trans h8) (Real.sqrt_nonneg b) (by linarith)
  · rw [min_eq_right (le_of_not_ge h),inv_div,div_eq_mul_inv]
    calc 4*l*z⁻¹ ≤ 4*(5^4*b^8)*z⁻¹ :=
           mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hwidth (by norm_num)) (inv_nonneg.mpr hz.le)
         _ ≤ overhead R*b^8 := by
           change _ ≤ (8+4*5^4*z⁻¹)*b^8
           nlinarith [pow_nonneg h0.le 8]

variable {V : Type} [Fintype V] [DecidableEq V] (d : V → ℕ)

theorem funded (simple : G.Simple) {ε : ℝ} {T : Campaign R}
    {W : Campaign.Pillars R T} (fund : FundedOriginalProperties.{u} simple ε W)
    (L : ℕ) (C M : ℝ) (v : ∀ i, R.family.label (d i))
    (href : ∀ i, R.family.ref (d i) ≤ L)
    (size : ∀ i, (R.family.labels.level (d i)).coeffSize (v i) ≤ M) (i : V) :
    let r := QLocalPhysicalBirthPurchase.debit R L (tolerance R L)
    (QLocalPhysicalBirthWeights.weight R L d v C r i)⁻¹ ≤
      (1 + stencil R d C * M) * overhead R * β₀ L^(pole R d + 8) := by
  dsimp only
  let b := β₀ L
  let r := QLocalPhysicalBirthPurchase.debit R L (tolerance R L)
  let x := ∑ j, QLocalPhysicalBirthWeights.exposure R L d v C j
  have hb : 1 ≤ b := ((A₀).fits.delayed L).le
  have hr : 0 < r := QLocalPhysicalBirthPurchase.debit_pos R L (tolerance_pos R L)
  have hx : x ≤ stencil R d C*b^(pole R d)*M :=
    cost R d L C M v (fund.2.1.paid.fixed L) (fund.2.1.logBudget.money.present L) size
  have hfirst : 1+x ≤ (1+stencil R d C*M)*b^(pole R d) := by
    rw [add_mul,one_mul]
    exact add_le_add (one_le_pow₀ hb) (hx.trans_eq (by ring))
  have hsum : 0 ≤ 1+x := by
    have hw := QLocalPhysicalBirthWeights.positive R L d v C hr href i
    change 0 < r/(1+x) at hw
    exact (pos_of_mul_pos_left (by simpa only [div_eq_inv_mul, mul_comm] using hw : 0 < (1+x)⁻¹*r) hr.le |> inv_pos.mp).le
  unfold QLocalPhysicalBirthWeights.weight
  change (r/(1+x))⁻¹ ≤ _
  rw [inv_div,div_eq_mul_inv]
  calc (1+x)*r⁻¹ ≤ ((1+stencil R d C*M)*b^(pole R d))*(overhead R*b^8) :=
         mul_le_mul hfirst (debit R L) (inv_nonneg.mpr hr.le) (hsum.trans hfirst)
       _ = _ := by rw [pow_add]; ring

end YM.Integration.WilsonOriginalCoordinateBirthRadius
