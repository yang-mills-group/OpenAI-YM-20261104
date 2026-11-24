import YM.Integration.WilsonEmittedSignedTariff
import YM.Integration.WilsonEmittedChildFinance
/-! The real original calendar pays simultaneously for every side and measured beta before the UV cutoff. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonEmittedOriginalCalendar
open Finset Filter RG Wilson Lattice QuadraticLocal QuadraticLocal.Advent RG.Supply PhysicalNext PhysicalNext.Repeat.Legato
open WilsonLimitConstruction FundedDictionaryPatchPrices WilsonEmittedDictionary WilsonEmittedStageFinance
open WilsonCoeffUV WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Physical WilsonCoeffUV.Bank.Mosaic
open Comparison.Density Comparison.Density.Mirrors Comparison.Density.Transport
open scoped Topology BigOperators
variable {G:Gauge} (tube:LinkTube G)

theorem wages (R:Run G) (simple:G.Simple) : ∀ᶠ i:ℕ in atTop,
    budgetR R i≤R.family.path.levels.clock.hatBeta i:=by
  let A:=R.family.path.levels
  have Hrise:Tendsto A.clock.hatBeta atTop atTop:=tendsto_atTop_add_const_left _ _
    (A.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos simple))
  filter_upwards [WilsonMeasuredSemesterSubpower.budget R 1 (by norm_num:0<(1/2:ℝ)),
    RG01.Physical.nextHat simple A,Hrise.eventually_ge_atTop 2] with i old next hH
  have nn:0≤budgetR R i:=zero_le_one.trans (budget_pos (R:=R) (i:=i))
  have paid:=old (budgetR R i) nn (min_le_right ..)
  rw [pow_one,←Real.sqrt_eq_rpow] at paid
  exact paid.trans ((Real.sqrt_le_iff).mpr ⟨by linarith,by change A.clock.hatBeta (i+1)≤(A.clock.hatBeta i)^2;nlinarith⟩)

theorem funded (R:Run G) (simple:G.Simple) (bought:Covered (program tube) R) (T k:ℕ)
    {cost δ:ℝ} (pos:0<δ) :
    let A:=R.family.path.levels
    ∀ᶠ i:ℕ in atTop,∀ per,∀β:ℝ,A.clock.hatBeta (i+1)/2≤β → β≤2*A.clock.hatBeta (i+1) →
      let H:=A.clock.hatBeta (i+1)
      let g:=(Real.sqrt β)⁻¹
      let b:=A.budget (i+1)
      let X:=(A.clock.op i per).patch
      let O:=A.params (i+1)
      let C:=program tube X A.clock.kernel O k
      let W:=WilsonEmittedCubeRoom.width A tube (i+1)
      1<H ∧ 0<β ∧ 0<g ∧ g≤1 ∧ cost*g≤δ ∧ 1≤Real.log H ∧
      (256*((T:ℝ)+1))^2≤Real.log H ∧ 0≤W ∧ W≤2*g^(1/2:ℝ) ∧
      Room b (A.S.side (i+1) per) tube (b.B+1) W ∧
      C≤Real.log H ∧ 2^(capacity X k)≤C ∧
      C^3*(1+Real.log H)^(orderBill X O k)≤g⁻¹ ∧ budgetR R (i+1)≤H := by
  let A:=R.family.path.levels
  have Hrise:Tendsto A.clock.hatBeta atTop atTop:=tendsto_atTop_add_const_left _ _
    (A.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos simple))
  have logRise:=Real.tendsto_log_atTop.comp Hrise
  have step:=tendsto_add_atTop_nat 1
  have grades:=WilsonEmittedStageFinance.funded tube R simple bought k (by norm_num:0<(1:ℝ))
  have span:=WilsonEmittedOriginalRoom.width_paid A tube simple (by norm_num:0<(1/2:ℝ))
  have room:=WilsonEmittedOriginalRoom.original A tube simple
  dsimp only
  filter_upwards [grades,bought k,step.eventually span,step.eventually room,
    step.eventually (logRise.eventually_ge_atTop ((256*((T:ℝ)+1))^2)),
    step.eventually (logRise.eventually_ge_atTop 1),
    step.eventually (Hrise.eventually_ge_atTop (2*((cost/δ)^2+1))),
    step.eventually (wages R simple)] with i money enrollment angular valid compact older hi wage
  intro per β lo up
  let H:=A.clock.hatBeta (i+1)
  have H1:1<H:=by unfold H;linarith [sq_nonneg (cost/δ)]
  have bb:0<β:=(half_pos (zero_lt_one.trans H1)).trans_le lo
  have enough:1≤β:=by linarith [sq_nonneg (cost/δ)]
  have small:cost*(Real.sqrt β)⁻¹≤δ:=by
    rw [←div_eq_mul_inv,div_le_iff₀ (Real.sqrt_pos.mpr bb)]
    rw [mul_comm]
    apply (div_le_iff₀ pos).mp
    apply Real.le_sqrt_of_sq_le
    linarith
  let X:=(A.clock.op i per).patch
  let O:=A.params (i+1)
  let C:=program tube X A.clock.kernel O k
  have use:C≤1+Real.log (Real.log (A.clock.hatBeta i)):=(le_abs_self _).trans (enrollment per).1
  have c:C≤Real.log H:=use.trans <| (by
    have a:=Real.log_le_sub_one_of_pos (Real.log_pos (A.fits.delayed i))
    have z:=Real.log_le_log (zero_lt_one.trans (A.fits.delayed i)) (WilsonCoeffUV.Layout.betaR A simple (Nat.le_succ i))
    dsimp only [H];linarith)
  have w0:0≤WilsonEmittedCubeRoom.width A tube (i+1):=by
    unfold WilsonEmittedCubeRoom.width
    have nn:=axial_nonneg (A.budget (i+1)) (WilsonEmittedCubeRoom.roof A (i+1))
    exact add_nonneg (A.budget (i+1)).threshold_pos.le (mul_nonneg (by linarith [tube.scale]) nn)
  refine ⟨H1,bb,inv_pos.mpr (Real.sqrt_pos.mpr bb),inv_le_one_of_one_le₀ (Real.one_le_sqrt.mpr enough),
    small,older,compact,w0,?_,valid per,c,(parts tube X A.clock.kernel O k).2.2.2.2.2,?_,wage⟩
  · convert angular β lo up using 1; norm_num
  · simpa only [Real.rpow_neg_one] using (money per β lo)

end YM.Integration.WilsonEmittedOriginalCalendar
end
