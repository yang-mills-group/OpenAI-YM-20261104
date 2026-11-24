import YM.Integration.WilsonMatrixTicketLanesConnectedIndependent
import YM.Integration.WilsonMatrixTicketLanesFundedScheme
import YM.Integration.WilsonWindowOriginalRun
import YM.Integration.WilsonWindowJointPurchase
import YM.Integration.WilsonMovingRoutedRegister
import YM.Integration.WilsonOldActionForecast
import YM.Integration.FundedOriginalVacuumPaths

/-! The physical company that pays the earlier registered action also purchases
the actual measured fields, signs and independent marked prescription. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
universe u
namespace YM.Integration.WilsonMatrixTicketLanesVacuumElection
open RG RG.Supply Precision Org Push.PriceCompiler
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Daisy.Charity.RG12
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open FVA2 FVA2.Register FVAAlt2 MS MS.Land
open IterationFour IterationFour.Vacuum
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark RegulatorIR.FVAAlt2.Lodge
open WilsonWindowJointPurchase
variable {G:Gauge}

def Earlier (v:ℕ→Gear G→ℝ):Prediction G:=fun {_} {_} {_} F=>
  WilsonFundedWindowCompany.PhysicalInputs F ∧ WilsonWindowReportingPace.Slow F ∧
  FundedMarkedCoverRows.prices v F ∧ FundedOriginalVacuumPaths.prices F ∧
  WilsonOldActionForecast.Eligible F ∧ WilsonMovingRoutedRegister.Earned (WilsonCoherentMayerCovarianceCalendar.decal G) F

private theorem physical {p:Prediction G} (price:FundedPredictionSupply.AllPrices (@p)):
    WilsonFundedWindowMenu.AllPrices (@p):=fun s t=>WilsonFundedWindowMenu.from_guard
    (WilsonFundedWindowCompany.of_prepaid (price s t))

theorem fees (simple:G.Simple) (v:ℕ→Gear G→ℝ):WilsonFundedWindowMenu.AllPrices (@Earlier G v):=by
  intro s t
  let m:=ThroughLaunch.raging s t
  exact joint (WilsonWindowOriginalRun.physical_inputs_paid s m) (joint (WilsonWindowReportingPace.prepaid simple s m)
    (joint (physical (FundedMarkedCoverRows.purchase v) s t) (joint (physical FundedOriginalVacuumPaths.buy s t)
      (joint (WilsonOldActionForecast.allPrices s t)
        (physical (WilsonMovingRoutedRegister.prepaid (WilsonCoherentMayerCovarianceCalendar.decal G)) s t)))))

/-- The independent prescription is fixed before the original run, its marked
codebook, its observing two-site packet or any earlier vacuum is selected. -/
theorem purchasedWith (simple:G.Simple) {ε:ℝ} (ep:0<ε) (v:ℕ→Gear G→ℝ) (calendar:XSpace.Run)
    (dial:Bool) (more:Prediction G) (future:WilsonFundedWindowMenu.AllPrices (@more)):
    ∃(N:WilsonPrescription G)(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
      (S:Prescription (Press.portDeck G)),N.run=calendar ∧ Main.Match N simple M S dial ∧
    ∃(R:Run G)(T:Campaign R)(W:Campaign.Pillars R T)
      (Q:Prescription (Press.portDeck G)),more R.kit ∧ Earlier v R.kit ∧
      FundedOriginalProperties.{u} simple ε W ∧ NativeFVAPlateau.Correlations R ∧
      Q.team=S.team ∧ TaylorOKPl M (Lobby.Table (basisR R) (Press.portDeck G)) Q ∧
      MixedStory.AllProfiles M (WilsonMatrixTicketLanesNativePrices.warehouse R) Q ∧
      WilsonMatrixTicketLanesConnectedIndependent.Measured R N simple Q:=by
  obtain ⟨N,M,S,date,matching⟩:=Main.solution G simple calendar dial
  let ticket:Prediction G:=@Together G (@more) (@Together G (@Earlier G v)
    (@Together G (@WilsonReportColumnSubsidy.Eligible G) (@Together G (@WilsonMatrixTicketLanesConnectedBudget.Paid G)
      (@WilsonMatrixTicketLanesReportedPrepaid.Paid G))))
  have buy:WilsonFundedWindowMenu.AllPrices (@ticket):=fun s t=>joint (future s t) (joint (fees simple v s t)
    (joint (WilsonReportColumnSubsidy.allPrices s t) (joint (physical WilsonMatrixTicketLanesConnectedBudget.allPrices s t)
      (physical WilsonMatrixTicketLanesReportedPrepaid.allPrices s t))))
  obtain ⟨R,T,W,stock,cor,funded⟩:=WilsonWindowOriginalRun.select.{u} simple ep (@ticket) buy
  obtain ⟨requested,early,subsidy,connected,report⟩:=stock
  obtain ⟨Q,team,taylor,story⟩:=WilsonMatrixTicketLanesFundedScheme.existing R N matching
  have bank:=WilsonGaussianProbeMatrix.measured W simple funded subsidy early.2.1 N Q
  exact ⟨N,M,S,date,matching,R,T,W,Q,requested,early,funded,cor,team,taylor,story,
    WilsonMatrixTicketLanesConnectedIndependent.on_run R N simple connected report early.2.1 Q bank⟩

end YM.Integration.WilsonMatrixTicketLanesVacuumElection
