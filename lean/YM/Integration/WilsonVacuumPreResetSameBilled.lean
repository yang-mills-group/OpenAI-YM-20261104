import YM.Integration.WilsonVacuumPreResetSameQuote
import YM.Integration.WilsonVacuumPreResetSameCurvature
import YM.Integration.WilsonVacuumPreResetModelBoard
import YM.Integration.WilsonPhysicalHistoryRetainedSpringTemperature

/-! The entire original upstream signed action has a before-volume source
tariff at its own physical heat and its own physical receiving budget.
Every issued list with the original height, width and count is admitted. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetSameBilled
open Filter Function Lattice RG Wilson WilsonStartup AnalyticBridge PhysicalNext PhysicalNext.Repeat Legato
open Pert.Asymptotics VerifiedReset RG01Estimate Time WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Physical WilsonLimitConstruction
open Collection Function Marker IterationFour.Vacuum Extra.Iteration Push Push.AbsoluteSums Push.AbsoluteSums.Animals Song Meadow
open WilsonVacuumPreResetRenderRank WilsonVacuumPreResetPeriodEntries
open scoped Topology BigOperators Classical
variable {G:Gauge}

theorem original (R:Run G)(simple:G.Simple)(v:ℕ→Gear G→ℝ)(rows:FundedMarkedCoverRows.prices v R.kit)
    (render:WilsonVacuumPreResetRenderCalendar.Issued R.kit)(income:WilsonVacuumPreResetPrecursorReserve.Issued R.kit)
    (time:RG01Estimate.Chart.Barrier R.alloy (fun _ i=>((i:ℝ)+1)⁻¹))(W:Credit)(r cap:ℕ){ε:ℝ}(ep:0<ε):
    let V:=R.family.path.levels
    ∀ᶠ m:ℕ in atTop,∀N per:ℕ,m<N→let g:=regulatorRun R.family N per m
      let p:=OriginalMarkedRunAction.finitePitch R N m r g
      let γ:=g^2*OriginalMarkedRunAction.pitchTail R N m r g
      let β:=γ+R.alloy.B.kin.alpha N m
      let C:=W.buy (zz V m)+zz V m*V.clock.loopCap m
      ∀(n:Side)(L:Listing G n)(σ:ℝ)(A:SeriesA G),0<σ→σ⁻¹≤zz V m→
        (∀a∈A,3≤a.grade ∧ a.grade≤cap)→A.length ≤ meterPre cap→∀t q,
        let T:=V.params m
        let B:=V.budget m
        let M:=WilsonVacuumPreResetModelBoard.source L B (R.alloy.B.kin.path N m) T.clip T.width T.paths γ β σ C A (weight g p) t q
        |M.bill|≤ε*Time.forecastE V m:=by
  intro V
  let K:ℝ:=meterPre cap*(12*2^(cap+2))
  have hp:0<ε/2:=half_pos ep
  obtain ⟨_,heat⟩:=OriginalMarkedRunAction.cofinal_temperature R simple v rows r
  filter_upwards [WilsonVacuumPreResetSameCurvature.original R simple v rows income time r hp,
    WilsonVacuumPreResetSameQuote.original R render simple W cap,
    WilsonVacuumPreResetSameTime.original R simple time K (by dsimp [K];positivity) hp,heat]
    with m curv funded clock temp
  intro N per later g p γ β C n L σ A pos width grades count t q T B M
  have h₁:=curv N per later B rfl rfl (by change T.supportExponent≤T.supportExponent+6;linarith) rfl
  obtain ⟨_,_,lo,hi,_,_⟩:=temp N later per
  have h₂:=funded N per later n (Song.headline B) σ p A pos width lo (hi.trans (by norm_num)) rfl rfl
    (by change T.supportExponent+3≤T.supportExponent+6;linarith) rfl grades
  have len:(A.length:ℝ) ≤ meterPre cap:=by exact_mod_cast count
  have fee:|quote (A.map (FundedCorrectedPeriod.piece n (Song.headline B) σ C)) (weight g p)|≤(ε/2)*Time.forecastE V m:=by
    apply h₂.trans
    apply le_trans _ (clock N per later)
    dsimp only [K]
    gcongr
    exact Real.rpow_nonneg (IterationFour.Currency.g_pos R.makes N per m later.le).le _
  change |WilsonVacuumPreResetCurvaturePrice.cost (G:=G) B T.clip T.width T.paths γ β+
    quote (A.map (FundedCorrectedPeriod.piece n (Song.headline B) σ C)) (weight g p)|≤_
  exact (abs_add_le ..).trans (by linarith only [h₁,fee])

end YM.Integration.WilsonVacuumPreResetSameBilled
