import YM.Integration.WilsonVacuumPreResetRenderReserve
import YM.Integration.WilsonVacuumPreResetLiftedClock

/-! A single original funding request covers every subsequent fixed rank and
every positive power allowance along the same physical course. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetRenderCalendar
open WilsonLimitConstruction Filter RG Wilson WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV.Bank.Ticket PhysicalNext.Repeat.Legato WilsonVacuumPreResetRenderReserve
open scoped Topology
variable {G:Gauge}

abbrev Issued : FundedCompanySelection.Prediction G:=
  Eligible (fun _ i=>i+2) (fun _ i=>((i:ℝ)+1)⁻¹)

theorem prepaid : FundedPredictionSupply.AllPrices (@Issued G):=
  WilsonVacuumPreResetRenderReserve.prepaid _ _ (by intro j i hi; positivity)

theorem original (R:Run G)(issued:Issued R.kit)(simple:G.Simple)(order:ℕ){η:ℝ}(ep:0<η):
    let V:=R.family.path.levels
    ∀ᶠ m:ℕ in atTop,1≤2*Real.log (V.clock.hatBeta m) ∧
      zz V (m+1) ≤ 2*Real.log (V.clock.hatBeta m) ∧
      ∀k≤order, amount G (V.params m) k (V.clock.hatBeta m) ≤ V.clock.hatBeta m ^ η:=by
  intro V
  let β:=V.clock.hatBeta
  obtain ⟨b,hb⟩:=exists_nat_gt η⁻¹
  have deep:=V.fits.deep
  have growth:=Real.tendsto_log_atTop.comp (RG01.Physical.hats simple V)
  filter_upwards [growth.eventually_ge_atTop 2,RG01.Physical.nextHat simple V,
    deep.eventually_ge_atTop order,deep.eventually_ge_atTop b] with m room next indexed far
  have room':2≤Real.log (β m):=room
  have pos:0<β m:=lt_trans zero_lt_one (V.fits.delayed m)
  have logNext:Real.log (β (m+1))≤2*Real.log (β m):=calc
    _ ≤ Real.log (2*β m):=Real.log_le_log (lt_trans zero_lt_one (V.fits.delayed _)) next
    _ = Real.log 2+Real.log (β m):=Real.log_mul (by norm_num) pos.ne'
    _ ≤ 2*Real.log (β m):=by linarith [Real.log_le_sub_one_of_pos (by norm_num :(0:ℝ)<2)]
  have lo:0<Real.log (β (m+1)):=Real.log_pos (V.fits.delayed _)
  have fuzz:zz V (m+1)≤2*Real.log (β m):=by
    change 1+Real.log (Real.log (β (m+1)))≤_
    linarith [Real.log_le_sub_one_of_pos lo]
  refine ⟨(show 1≤2*Real.log (β m) by linarith),fuzz,?_⟩
  intro k hk
  have within:k≤V.clock.J m+2:=by omega
  have raw:=issued m k within
  apply raw.trans
  apply Real.rpow_le_rpow_of_exponent_le (V.fits.delayed m).le
  have hi:(b:ℝ)≤(V.clock.J m:ℝ):=by exact_mod_cast far
  have one:η⁻¹≤(V.clock.J m:ℝ)+1:=by linarith
  exact (inv_le_comm₀ (by positivity) ep).2 one

end YM.Integration.WilsonVacuumPreResetRenderCalendar
