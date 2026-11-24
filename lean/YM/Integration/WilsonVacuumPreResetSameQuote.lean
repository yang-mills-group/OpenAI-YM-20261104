import YM.Integration.WilsonVacuumPreResetRenderQuote
import YM.Integration.WilsonVacuumPreResetSameIncome

/-! At each upstream date, the issued corrected ranks pay their original
spatial and derivative tariffs at the measured temperature of that date. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetSameQuote
open Filter Lattice RG Wilson WilsonStartup Pert.Asymptotics PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV.Physical WilsonLimitConstruction IterationFour.Vacuum WilsonVacuumPreResetPeriodEntries
open WilsonVacuumPreResetRenderRank WilsonVacuumPreResetRenderCalendar
open scoped Classical Topology BigOperators
variable {G:Gauge}{n:Side}

open private sum tax from YM.Integration.WilsonVacuumPreResetRenderQuote

theorem original (R:Run G)(issued:Issued R.kit)(simple:G.Simple)(W:Credit)(cap:ℕ):
    let V:=R.family.path.levels
    ∀ᶠ m:ℕ in atTop,∀N per:ℕ,m<N→
      let g:=regulatorRun R.family N per m
      let C:=W.buy (zz V m)+zz V m*V.clock.loopCap m
      ∀ (n:Side)(B:BudgetPoint)(σ p:ℝ)(Z:SeriesA G),0<σ→σ⁻¹≤zz V m→
      1/2≤p→p≤2→B.order=(V.params m).order→B.power=(V.params m).power→
      B.supportExponent≤(V.params m).supportExponent+6→B.threshold=(V.budget m).threshold→
      (∀a∈Z,3≤a.grade ∧ a.grade≤cap)→
      |quote (Z.map (FundedCorrectedPeriod.piece n B σ C)) (weight g p)|≤
        Z.length*(12*2^(cap+2))*g^(11/4:ℝ):=by
  intro V
  let η:ℝ:=(4*((cap:ℝ)+5))⁻¹
  have ep:0<η:=by dsimp [η];positivity
  have rate:η≤1:=by
    dsimp [η]
    apply inv_le_one_of_one_le₀
    linarith [Nat.cast_nonneg (α:=ℝ) cap]
  filter_upwards [WilsonVacuumPreResetRenderCalendar.original R issued simple (cap+2) ep,
    WilsonVacuumPreResetSameIncome.original R simple W ep] with m calendar income
  intro N per later g C n B σ p Z sp sw lo hi order power exponent threshold bounded
  let A:=g^(-η)
  obtain ⟨gp,unit,cash,angle,charged⟩:=income N per later
  have one:1≤A:=Real.one_le_rpow_of_pos_of_le_one_of_nonpos gp unit (neg_nonpos.mpr ep.le)
  have bt:=tax gp ep rate charged (zero_le_one.trans (V.fits.delayed m).le) (rfl:A=g^(-η))
  have group:g^3*A^(cap+5)=g^(11/4:ℝ):=by
    rw [←Real.rpow_natCast g 3,←Real.rpow_mul_natCast gp.le (-η) (cap+5),←Real.rpow_add gp]
    congr 1
    push_cast
    dsimp [η]
    field_simp
    ring
  calc
    _ ≤ Z.length*(12*2^(cap+2)*g^3*A^(cap+5)):=sum n B σ C g p _ Z fun a ha=>by
      have h:=bounded a ha
      have k:a.rise+2≤cap+2:=by have l:=a.rankA;omega
      apply atom B a σ C g p A cap gp unit one lo hi h.1 h.2 (threshold ▸ angle) cash
      apply (WilsonVacuumPreResetRenderDebit.original (V.params m) B order power exponent
        _ σ C sp calendar.1 ((sw.trans (WilsonVacuumPreResetPrecursorIncome.width V simple m)).trans calendar.2.1) a).trans
      have price:WilsonVacuumPreResetRenderReserve.amount G (V.params m) (a.rise+2) (V.clock.hatBeta m)≤2*A^2:=
        (calendar.2.2 _ k).trans bt
      gcongr
      exact pow_nonneg B.threshold_pos.le _
    _ = _:=by rw [←group];ring

end YM.Integration.WilsonVacuumPreResetSameQuote
