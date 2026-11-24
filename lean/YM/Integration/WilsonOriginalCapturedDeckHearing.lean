import YM.Integration.WilsonOriginalCapturedPageProduct
import YM.Integration.WilsonOriginalRelativePageIncome
import YM.Integration.OriginalPeriodWindingPrice

/-! A quantitative angular comparison on the physical course, including its
flat coefficient. The auxiliary side and the held directions are chosen after the physical threshold. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonOriginalCapturedDeckHearing
open Lattice RG Finset Filter Further.PhysicalPeriodLimitF933 Macrame FVA1Physical TwoReset
open ActualRunAdmissionScales Pert.Asymptotics PhysicalNext.Repeat.Legato
open WilsonOriginalConnectedPeriodPage WilsonOriginalOccupiedAngularPage WilsonOriginalPolarizedAngularPage
open WilsonOriginalLinkedAngularPage
open scoped BigOperators Classical
variable {G:Gauge}

private theorem quiet {n X:Side} (h:n.val∣X.val) (o:Site X)(F:Stationary.Link G X→ℂ):
    board h o (move G) F 0=∑_:Deck h,F 0:=by
  calc
    _ = ∑u:Fin (Pages n X),F 0:=by simp [board]
    _ = _ :=pages h o (fun _=>F 0)

theorem flat {n X:Side} (h:n.val∣X.val) (o z:Site X) (F Z:Stationary.Link G X→ℂ)
    (ground:board h o (move G) F 0=board h z (move G) Z 0):F 0=Z 0:=by
  apply sub_eq_zero.mp
  apply constant h
  rw [sum_sub_distrib,sub_eq_zero,←quiet h o F,←quiet h z Z]
  exact ground

/-- A finite physical-period fiber error, paid on the selected Run through
any fixed coupling order before both the UV cutoff and every physical period. -/
theorem original (R:Run G) (simple:G.Simple) (fund:RG05Preconstruction.ReadoutPurchase R.b)
    (a c q r:ℕ) (j:Fin r):∀ᶠ m:ℕ in atTop,∀ N per:ℕ,m<N →
    let n:=R.family.side m per
    let g:=regulatorRun R.family N per (m+1)
    let C:=admittedCost R.family.path.levels m
    ∀(X:Side)(h:n.val∣X.val)(root left right:Site X)(F Z:Stationary.Link G X→ℂ),
    ContDiff ℝ r F → ContDiff ℝ r Z → (∀ A,board h left (move G) F A=board h right (move G) Z A) →
    ∀(span:Positions X (Stationary.Loc G 1) r→ℝ)(ρ D spent fare:ℝ),
    0<ρ → ρ⁻¹ ≤ C → D ≤ (n.val:ℝ)/8 → (∀x,(separation root (x j).1:ℝ) ≤ span x+D) →
    (∑x,Real.exp (ρ*span x)*‖coefficient r F x‖) ≤ spent →
    (∑x,Real.exp (ρ*span x)*‖coefficient r Z x‖) ≤ fare →
    2*(spent+fare) ≤ C^a*g^(-(c:ℝ)) →
    (∑x,Real.exp (ρ*span x/2)*‖coefficient r F x-coefficient r Z x‖) ≤ g^q:=by
  filter_upwards [OriginalPeriodWindingPrice.onRun R simple fund a c q] with m stage
  intro N per late n g C X h root left right F Z sm booked binding span ρ D spent fare positive width short paths original prior wallet
  have paid:=WilsonOriginalLinkedAngularPage.original h root left right j F Z sm booked binding span paths short positive.le original prior
  have rate:=stage N per late ρ positive width
  have npos:0 ≤ ((R.family.side m per).val:ℝ):=Nat.cast_nonneg _
  have small:Real.exp (-(ρ*((R.family.side m per).val:ℝ))/8) ≤
      Real.exp (-(ρ/512)*(R.family.side m per).val):=by
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_nonneg positive.le npos]
  calc
    _ ≤ 2*Real.exp (-(ρ*(R.family.side m per).val)/8)*(spent+fare):=paid
    _ = (2*(spent+fare))*Real.exp (-(ρ*(R.family.side m per).val)/8):=by ring
    _ ≤ _ :=(mul_le_mul wallet small (Real.exp_pos _).le (mul_nonneg
      (pow_nonneg ((zero_le_one:0≤(1:ℝ)).trans (admittedCost_one _ _)) _) (Real.rpow_nonneg
      (show 0 ≤ regulatorRun R.family N per (m+1) from inv_nonneg.mpr (Real.sqrt_nonneg _)) _))).trans rate

end YM.Integration.WilsonOriginalCapturedDeckHearing
