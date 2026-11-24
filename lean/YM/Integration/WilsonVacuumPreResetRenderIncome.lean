import YM.Integration.WilsonVacuumPreResetRenderCalendar
import YM.Integration.WilsonVacuumPreResetRenderDebit
import YM.Integration.WilsonPhysicalHistoryRetainedSpringTemperature

/-! The original covering constant and both the coarse threshold and the full
derivative debit are spent at the measured incoming cutoff temperature. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetRenderIncome
open Filter Lattice RG Wilson WilsonStartup Pert.Asymptotics
open PhysicalNext.Repeat.Legato WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Physical WilsonLimitConstruction
open scoped Topology
variable {G:Gauge}

private theorem monitor (A:Levels G)(simple:G.Simple){η:ℝ}(ep:0<η):
    ∀ᶠ m:ℕ in atTop,∀b:ℝ,A.clock.hatBeta m/2≤b→
      A.clock.monitor m ≤ ((Real.sqrt b)⁻¹)^(-η):=by
  let S:Credit:=⟨2,1,le_rfl⟩
  filter_upwards [exp_at_band S A simple η ep,(stamp_lim A simple).eventually_ge_atTop 1] with m paid large
  intro b band
  apply le_trans _ (paid b band)
  rw [time_change]
  apply Real.exp_le_exp.mpr
  change (zz A m-1)^2≤1*(zz A m)^2
  nlinarith

theorem original (R:Run G)(simple:G.Simple)(W:Credit){η:ℝ}(ep:0<η):
    let V:=R.family.path.levels
    ∀ᶠ m:ℕ in atTop,∀N n:ℕ,m<N→
      let j:=m+1
      let g:=regulatorRun R.family N n j
      let C:=W.buy (zz V j)+zz V j*V.clock.loopCap j
      0<g ∧ g≤1 ∧ |C|≤3*g^(-η) ∧
        (V.budget m).threshold≤2*g*g^(-η) ∧ V.clock.hatBeta m≤2*(g^2)⁻¹:=by
  intro V
  filter_upwards [monitor V simple ep,(tendsto_add_atTop_nat 1).eventually (monitor V simple ep),
    (tendsto_add_atTop_nat 1).eventually (retaining_expense simple V W Credit.leanC 1 zero_lt_one),
    (tendsto_add_atTop_nat 1).eventually ((stamp_lim V simple).eventually_ge_atTop 1),
    (RG01.Physical.hats simple V).eventually_ge_atTop 2,RG01.Physical.nextHat simple V] with m coarse fine cash big room next
  intro N n later
  let β:=R.family.path.β N n (m+1)
  let b:=V.clock.hatBeta m
  let c:=V.clock.hatBeta (m+1)
  let g:=(Real.sqrt β)⁻¹
  have mono:b≤c:=Timing.hat_mono V (Gauge.slopeConstant_pos simple).le m.le_succ
  have bpos:0<b:=zero_lt_one.trans (V.fits.delayed m)
  have band:= (R.makes.wilson.represents N n (m+1) later).band
  have lower:c/2≤β:=band.1
  have upper:β≤2*c:=band.2
  have cnext:c≤2*b:=next
  have above:2≤b:=room
  have positive:0<β:=by linarith
  have gp:0<g:=inv_pos.mpr (Real.sqrt_pos.mpr positive)
  have sq:Real.sqrt β ^2=β:=Real.sq_sqrt positive.le
  have heat:g≤1:=by
    apply inv_le_one_of_one_le₀
    exact (Real.le_sqrt (by norm_num) positive.le).2 (by nlinarith)
  have bank:W.buy (zz V (m+1))+zz V (m+1)*V.clock.loopCap (m+1)≤3*V.clock.monitor (m+1):=by
    simpa [Credit.leanC,Credit.buy,Real.rpow_one] using cash
  have cash0:0≤W.buy (zz V (m+1))+zz V (m+1)*V.clock.loopCap (m+1):=by
    have z:1≤zz V (m+1):=big
    have loop:0≤V.clock.loopCap (m+1):=by unfold Calendar.loopCap Calendar.monitor; positivity
    exact add_nonneg (zero_le_one.trans (W.purchase z)) (mul_nonneg (zero_le_one.trans z) loop)
  have cm:V.clock.monitor m≤g^(-η):=coarse β (by linarith)
  have fm:V.clock.monitor (m+1)≤g^(-η):=fine β lower
  have square:Real.sqrt β≤2*Real.sqrt b:=(Real.sqrt_le_left (by positivity)).mpr
    (by nlinarith only [upper,cnext,Real.sq_sqrt bpos.le,bpos.le])
  have inv:(Real.sqrt b)⁻¹≤2*g:=by
    rw [←one_div,show 2*g=2/Real.sqrt β by rw [div_eq_mul_inv]]
    exact (div_le_div_iff₀ (Real.sqrt_pos.mpr bpos) (Real.sqrt_pos.mpr positive)).2 (by simpa using square)
  refine ⟨gp,heat,(abs_of_nonneg cash0).trans_le (bank.trans (mul_le_mul_of_nonneg_left fm (by norm_num))),?_,?_⟩
  · change (Real.sqrt b)⁻¹*V.clock.monitor m≤2*g*g^(-η)
    exact mul_le_mul inv cm (Real.exp_pos _).le (by positivity)
  · change b≤2*(g^2)⁻¹
    dsimp only [g]
    rw [inv_pow,inv_inv,sq]
    linarith

end YM.Integration.WilsonVacuumPreResetRenderIncome
