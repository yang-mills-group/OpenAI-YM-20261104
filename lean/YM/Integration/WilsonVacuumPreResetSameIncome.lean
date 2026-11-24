import YM.Integration.WilsonVacuumPreResetRenderIncome
import YM.Integration.WilsonVacuumPreResetPrecursorIncome

/-! Thermal and source prices for the retained action at its own original
date and its own original coupling, on all physical upper cutoffs. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetSameIncome
open Filter Lattice Wilson RG WilsonStartup Pert.Asymptotics PhysicalNext.Repeat.Legato
open AnalyticBridge VerifiedReset RG01Estimate WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Physical WilsonLimitConstruction
open private monitor from YM.Integration.WilsonVacuumPreResetRenderIncome
open scoped Topology
variable {G:Gauge}

theorem original (R:Run G)(simple:G.Simple)(W:Credit){η:ℝ}(ep:0<η):
    let V:=R.family.path.levels
    ∀ᶠ m:ℕ in atTop,∀N n:ℕ,m<N→
      let g:=regulatorRun R.family N n m
      let C:=W.buy (zz V m)+zz V m*V.clock.loopCap m
      0<g ∧ g≤1 ∧ |C|≤3*g^(-η) ∧
        (V.budget m).threshold≤2*g*g^(-η) ∧ V.clock.hatBeta m≤2*(g^2)⁻¹:=by
  intro V
  filter_upwards [monitor V simple ep,retaining_expense simple V W Credit.leanC 1 zero_lt_one,
    (stamp_lim V simple).eventually_ge_atTop 1,(RG01.Physical.hats simple V).eventually_ge_atTop 2]
    with m fiscal cash big room
  intro N n later
  let β:=R.family.path.β N n m
  let b:=V.clock.hatBeta m
  let g:=(Real.sqrt β)⁻¹
  have bpos:0<b:=zero_lt_one.trans (V.fits.delayed m)
  have band:=(R.makes.wilson.represents N n m later.le).band
  have lower:b/2≤β:=band.1
  have upper:β≤2*b:=band.2
  have above:2≤b:=room
  have positive:0<β:=by linarith
  have gp:0<g:=inv_pos.mpr (Real.sqrt_pos.mpr positive)
  have sq:Real.sqrt β ^2=β:=Real.sq_sqrt positive.le
  have heat:g≤1:=by
    apply inv_le_one_of_one_le₀
    exact (Real.le_sqrt (by norm_num) positive.le).2 (by nlinarith)
  have bank:W.buy (zz V m)+zz V m*V.clock.loopCap m≤3*V.clock.monitor m:=by
    simpa [Credit.leanC,Credit.buy,Real.rpow_one] using cash
  have cash0:0≤W.buy (zz V m)+zz V m*V.clock.loopCap m:=by
    have loop:0≤V.clock.loopCap m:=by unfold Calendar.loopCap Calendar.monitor;positivity
    exact add_nonneg (zero_le_one.trans (W.purchase big)) (mul_nonneg (zero_le_one.trans big) loop)
  have fm:V.clock.monitor m≤g^(-η):=fiscal β lower
  have square:Real.sqrt β≤2*Real.sqrt b:=(Real.sqrt_le_left (by positivity)).mpr
    (by nlinarith only [upper,Real.sq_sqrt bpos.le,bpos.le])
  have inv:(Real.sqrt b)⁻¹≤2*g:=by
    rw [←one_div,show 2*g=2/Real.sqrt β by rw [div_eq_mul_inv]]
    exact (div_le_div_iff₀ (Real.sqrt_pos.mpr bpos) (Real.sqrt_pos.mpr positive)).2 (by simpa using square)
  refine ⟨gp,heat,(abs_of_nonneg cash0).trans_le (bank.trans (mul_le_mul_of_nonneg_left fm (by norm_num))),?_,?_⟩
  · change (Real.sqrt b)⁻¹*V.clock.monitor m≤2*g*g^(-η)
    exact mul_le_mul inv fm (Real.exp_pos _).le (by positivity)
  · change b≤2*(g^2)⁻¹
    dsimp only [g]
    rw [inv_pow,inv_inv,sq]
    linarith

end YM.Integration.WilsonVacuumPreResetSameIncome
