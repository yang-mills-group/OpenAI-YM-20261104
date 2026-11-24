import YM.Integration.WilsonVacuumPreResetRenderIncome

/-! The covering width and its coefficient income at the landing date use
the true fine physical coupling in the original pre-reset evaluation. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetPrecursorIncome
open Filter Lattice RG Wilson WilsonStartup Pert.Asymptotics
open PhysicalNext.Repeat.Legato WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Physical WilsonLimitConstruction
open scoped Topology
variable {G:Gauge}


open private monitor from YM.Integration.WilsonVacuumPreResetRenderIncome

theorem width (V:Levels G)(simple:G.Simple)(m:ℕ):zz V m≤zz V (m+1):=by
  change 1+Real.log (Real.log (V.clock.hatBeta m))≤1+Real.log (Real.log (V.clock.hatBeta (m+1)))
  gcongr
  · exact Real.log_pos (V.fits.delayed _)
  · exact zero_lt_one.trans (V.fits.delayed _)
  · exact Timing.hat_mono V (Gauge.slopeConstant_pos simple).le m.le_succ

theorem capital (R:Run G)(simple:G.Simple)(W:Credit){η:ℝ}(ep:0<η):
    let V:=R.family.path.levels
    ∀ᶠ m:ℕ in atTop,∀N per:ℕ,m<N→
      let g:=regulatorRun R.family N per (m+1)
      |W.buy (zz V m)+zz V m*V.clock.loopCap m| ≤3*g^(-η):=by
  intro V
  filter_upwards [monitor V simple ep,retaining_expense simple V W Credit.leanC 1 zero_lt_one,
    (stamp_lim V simple).eventually_ge_atTop 1] with m fiscal cash big
  intro N n later g
  have mono:=Timing.hat_mono V (Gauge.slopeConstant_pos simple).le m.le_succ
  have lower:V.clock.hatBeta (m+1)/2≤R.family.path.β N n (m+1):=(R.makes.wilson.represents N n (m+1) later).band.1
  have own:=fiscal (R.family.path.β N n (m+1)) (by linarith)
  have bank:W.buy (zz V m)+zz V m*V.clock.loopCap m≤3*V.clock.monitor m:=by
    simpa [Credit.leanC,Credit.buy,Real.rpow_one] using cash
  have cash0:0≤W.buy (zz V m)+zz V m*V.clock.loopCap m:=by
    have z:1≤zz V m:=big
    have loop:0≤V.clock.loopCap m:=by unfold Calendar.loopCap Calendar.monitor; positivity
    exact add_nonneg (zero_le_one.trans (W.purchase z)) (mul_nonneg (zero_le_one.trans z) loop)
  exact (abs_of_nonneg cash0).trans_le (bank.trans (mul_le_mul_of_nonneg_left own (by norm_num)))

end YM.Integration.WilsonVacuumPreResetPrecursorIncome
