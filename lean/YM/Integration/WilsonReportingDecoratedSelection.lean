import YM.Integration.WilsonReportingRetainedAngularElection
import YM.Integration.WilsonReportingDecoratedAppointment

/-! The complete angular, old-sector and decorated-word appointment on one
original run, retaining a separately prepaid additional prediction. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReportingDecoratedSelection
open Function Filter Set Finset Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org
open PhysicalNext PhysicalNext.Repeat Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost
open PhysicalNext.Repeat.Legato
open WilsonLimitConstruction.FundedCompanySelection
open scoped Classical Topology BigOperators
open WilsonLimitConstruction WilsonReportingForestAngularFare WilsonReportingForestAngularReflection
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric QLocalRequestedSectorCalendar
open WilsonOriginalMarkedExistence PhysicalNext.Repeat.Daisy.Charity.RG12
open Filter RG RG.Supply Precision Org Push.PriceCompiler Lattice
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Daisy.Charity.RG12 GapsLocal.Renew
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
universe u
variable {G : Gauge} {V : Type}

open Push.SectorMeasure
theorem selected [DecidableEq V] [Fintype V] (simple : G.Simple) {ε : ℝ} (hε : 0 < ε)
    (J : Request V) (χ : Chi) (extra : Stage → ℕ → ℝ) (γ : ℝ) (hγ : -(1/2:ℝ) < γ)
    (more : Prediction G) (offered : FundedPredictionSupply.AllPrices (@more)) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T)
        (_ : QLocalRequestedSectorCalendar.Paid J (WilsonReportingDecoratedStage.joined G J χ) extra γ R.kit),
    posted R ∧ more R.kit ∧ WilsonOriginalHighSelection.Salary G R.kit ∧
      Stationary.LightPath R.alloy.B.kin Real.log ∧
      Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay ∧
      Mallow.RG12.Earned (checkout G) R.kit.shape R.alloy.delay ∧
      NativeFVAPlateau.Correlations R ∧ FundedOriginalProperties.{u} simple ε W ∧ Charged R := by
  let sector : Prediction G := @QLocalRequestedSectorCalendar.Paid G V J (WilsonReportingDecoratedStage.joined G J χ) extra γ
  obtain ⟨R,T,W,⟨paid,angle,other⟩,salary,light,marks,checks,correlations,funded,charged⟩ :=
    WilsonOriginalHighLightRun.selectedWith.{u} WilsonOriginalLogLight.movable simple hε
      (@FundedPredictionSupply.Both G (@sector) (@FundedPredictionSupply.Both G (@WilsonReportingRetainedAngularElection.invoice G) (@more)))
      (fun s t => FundedPredictionSupply.both
        (QLocalRequestedSectorCalendar.prepaid J (WilsonReportingDecoratedStage.joined G J χ) extra γ simple hγ s
          (ThroughLaunch.raging s t))
        (FundedPredictionSupply.both (WilsonReportingRetainedAngularElection.prepaid G s t) (offered s t)))
  exact ⟨R,T,W,paid,angle,other,salary,light,marks,checks,correlations,funded,charged⟩

end YM.Integration.WilsonReportingDecoratedSelection
