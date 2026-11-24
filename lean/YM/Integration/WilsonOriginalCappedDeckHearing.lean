import YM.Integration.WilsonOriginalCapturedDeckHearing
import YM.Integration.WilsonOriginalPolynomialWinding

/-! A quantitative angular comparison on the physical course, including its
flat coefficient. The auxiliary side and the held directions are chosen after the physical threshold. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonOriginalCappedDeckHearing
open Lattice RG Finset Filter Further.PhysicalPeriodLimitF933 Macrame FVA1Physical TwoReset
open ActualRunAdmissionScales Pert.Asymptotics PhysicalNext.Repeat.Legato
open WilsonOriginalConnectedPeriodPage WilsonOriginalOccupiedAngularPage WilsonOriginalPolarizedAngularPage
open WilsonOriginalLinkedAngularPage
open scoped BigOperators Classical
variable {G:Gauge}

/-- A finite physical-period fiber error, paid on the selected Run through
any fixed coupling order before both the UV cutoff and every physical period. -/
theorem original (R:Run G) (simple:G.Simple) (fund:RG05Preconstruction.ReadoutPurchase R.b)
    (a b c q r:ℕ) (j:Fin r):∀ᶠ m:ℕ in atTop,∀ N per:ℕ,m<N →
    let n:=R.family.side m per
    let g:=regulatorRun R.family N per (m+1)
    let H:=R.family.path.levels.clock.hatBeta m
    ∀(X:Side)(h:n.val∣X.val)(root left right:Site X)(F Z:Stationary.Link G X→ℂ),
    ContDiff ℝ r F → ContDiff ℝ r Z → (∀ A,board h left (move G) F A=board h right (move G) Z A) →
    ∀(span:Positions X (Stationary.Loc G 1) r→ℝ)(ρ D spent fare:ℝ),
    0<ρ → ρ⁻¹ ≤ H^b → D ≤ (n.val:ℝ)/8 → (∀x,(separation root (x j).1:ℝ) ≤ span x+D) →
    (∑x,Real.exp (ρ*span x)*‖coefficient r F x‖) ≤ spent →
    (∑x,Real.exp (ρ*span x)*‖coefficient r Z x‖) ≤ fare →
    2*(spent+fare) ≤ H^a*g^(-(c:ℝ)) →
    (∑x,Real.exp (ρ*span x/2)*‖coefficient r F x-coefficient r Z x‖) ≤ g^q:=by
  filter_upwards [WilsonOriginalPolynomialWinding.original R simple fund a b c q] with m stage
  intro N per late n g H X h root left right F Z sm booked binding span ρ D spent fare positive width short paths original prior wallet
  have paid:=WilsonOriginalLinkedAngularPage.original h root left right j F Z sm booked binding span paths short positive.le original prior
  have rate:=stage N per late ρ positive width
  calc
    _ ≤ 2*Real.exp (-(ρ*(R.family.side m per).val)/8)*(spent+fare):=paid
    _ = (2*(spent+fare))*Real.exp (-(ρ*(R.family.side m per).val)/8):=by ring
    _ ≤ _ := (mul_le_mul_of_nonneg_right wallet (Real.exp_pos _).le).trans rate

/-- A strip with the co-issued exponential threshold fits a polynomial
inverse-width lease on that same date, even after fixed narrowing. -/
theorem width {H σ:ℝ} (hs:0<σ) (leased:Real.exp ((σ⁻¹)^2) ≤ H)
    {C:ℝ} (cp:0<C) (late:C≤H) : 0 < min 1 (σ/C) ∧ (min 1 (σ/C))⁻¹≤H^2:=by
  refine ⟨lt_min zero_lt_one (div_pos hs cp),?_⟩
  have wage:σ⁻¹≤H:=by
    have positive:=Real.add_one_le_exp ((σ⁻¹)^2)
    nlinarith only [positive,leased,sq_nonneg (σ⁻¹-1/2)]
  have hm:1≤H:= (Real.one_le_exp (sq_nonneg _)).trans leased
  rcases le_total 1 (σ/C) with h|h
  · rw [min_eq_left h,inv_one]
    nlinarith only [hm,sq_nonneg (H-1)]
  · rw [min_eq_right h,inv_div,div_eq_mul_inv,pow_two]
    exact mul_le_mul late wage (inv_nonneg.mpr hs.le) (zero_le_one.trans hm)

end YM.Integration.WilsonOriginalCappedDeckHearing
