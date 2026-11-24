import YM.Integration.WilsonGaussianFundedMS
import YM.Integration.WilsonInvariantActionCaptureRun

/-! The taxpayer for the separated physical Wilson products is chosen before the same run as the signed MS and local Gaussian data. -/
noncomputable section
set_option autoImplicit false

namespace YM.Integration.WilsonGaussianCitizenMS
open Filter Function Lattice Wilson Pressure RG Marker Precision ConnectedActivityE6
open ConnectedActivityE6.Blaze Blaze.March Captain Extra.Multi
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.JointLoad
open Heir Heir.Suite Push.PriceCompiler Supply Testing Push.SectorMeasure Push
open IterationFour IterationFour.Vacuum LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open QLocalRequestedHeirQuote QLocalRequestedSectorSale QLocalRequestedSectorCalendar
open PhysicalNext.Repeat.Opera PhysicalNext.Repeat.Daisy
open MergeProof LocalLTE
open scoped Topology BigOperators Classical

open RGLocalTaylor RGLocalTaylor.Laminate

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {Γ : Marker.Census V}

open FVA2 FVA2.CityHistory FVA2.Register FVAAlt2 FormalOPE.RG10.BlockGauge
open MS MS.Rake MS.Land MS.Tide MS.Orbit MS.Dial MS.Fleet MS.Local.Physical
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open ManuscriptQLocalCofinalAffineFields (schedule)
universe u
open RG RG.Supply Precision Org Push.PriceCompiler
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonLimitConstruction.FundedCompanySelection


private theorem column_prices {G : Gauge} :
    FundedPredictionSupply.AllPrices (@WilsonReportColumnSubsidy.Eligible G) := by
  intro s t targets expenses chart programs wages baton fees
  refine ⟨0, ?_⟩
  intro l hl D w U Z post scouts θ stages cost V quarter
  obtain ⟨W,hVW,grant⟩ := subsidize_feasible (G:=G) V
  refine ⟨W,hVW,?_⟩
  intro Y hY bar wait priced B
  dsimp only
  intro η q exchange menu aux rider booth sheltered works divides
  exact grant Y hY wait B.a B.valid

theorem purchased {G : Gauge} {V : Type} [Fintype V] [DecidableEq V]
    (simple : G.Simple) {ε : ℝ} (hε : 0 < ε) (J : Request V) (χ : Chi)
    (extra : Stage → ℕ → ℝ) (γ : ℝ) (hγ : -(1/2:ℝ) < γ) (calendar : XSpace.Run) (dial : Bool) :
    ∃ (N : WilsonPrescription G) (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
      (S : Prescription (Press.portDeck G)), N.run=calendar ∧ Main.Match N simple M S dial ∧
      ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T)
        (affine : ManuscriptQLocalCofinalAffineFields.Paid R) (Q : Prescription (Press.portDeck G))
        (orders : ManuscriptQLocalScalarDirections.PaidOrders schedule schedule R.kit)
        (table : WilsonScalarSourceTableForecast.Paid schedule schedule R.kit)
        (booking : QLocalRequestedSectorCalendar.Paid J
          (WilsonGaussianDeterminantTender.joined G J χ (WilsonCoherentMayerCovarianceCalendar.decal G))
          extra γ R.kit),
        PhysicalNext.Repeat.Legato.Citizen R.family R.w
          (PhysicalNext.Repeat.Legato.Bandage.mutt R.family.path.levels R.Q) R.doors ∧
        WilsonRootedPhysicalSpringReportedMS.Settled.{u} simple ε J extra γ M S R T W affine Q ∧
        WilsonRootedPhysicalSpringStoredMS.Ready simple M R affine Q orders ∧
        WilsonRootedPhysicalSpringUnitMS.Ready simple M R affine Q table ∧
        WilsonGaussianDeterminantQuarticMS.Common simple R J χ extra γ M Q affine orders booking ∧
        WilsonRootedPhysicalSpringAccurateMS.Ready simple M R affine Q table ∧
        WilsonGaussianSourceMS.Common simple R J χ extra γ M Q affine table booking := by
  obtain ⟨N,M,S,clock,matched,R,T,W,affine,Q,orders,table,booking,subsidy,settled,remaining⟩ :=
    WilsonGaussianFundedMS.purchasedWith.{u} simple hε J χ extra γ hγ calendar dial
      (@WilsonReportColumnSubsidy.Eligible G) column_prices
  have citizen := WilsonInvariantActionCaptureRun.on_run simple W settled.1.original subsidy
  exact ⟨N,M,S,clock,matched,R,T,W,affine,Q,orders,table,booking,citizen,settled,remaining⟩

end YM.Integration.WilsonGaussianCitizenMS
