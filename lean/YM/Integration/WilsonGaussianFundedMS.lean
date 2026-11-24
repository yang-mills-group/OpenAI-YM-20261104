import YM.Integration.WilsonGaussianSourceMS

/-! The all-order signed Gaussian source comparison and a second forecast are bought on the same original Wilson run. -/
noncomputable section
set_option autoImplicit false

namespace YM.Integration.WilsonGaussianFundedMS
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
theorem purchasedWith {G : Gauge} {V : Type} [Fintype V] [DecidableEq V]
    (simple : G.Simple) {ε : ℝ} (hε : 0 < ε) (J : Request V) (χ : Chi)
    (extra : Stage → ℕ → ℝ) (γ : ℝ) (hγ : -(1/2:ℝ) < γ) (calendar : XSpace.Run) (dial : Bool)
    (prediction : Prediction G) (price : FundedPredictionSupply.AllPrices (@prediction)) :
    ∃ (N : WilsonPrescription G) (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
      (S : Prescription (Press.portDeck G)), N.run=calendar ∧ Main.Match N simple M S dial ∧
      ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T)
        (affine : ManuscriptQLocalCofinalAffineFields.Paid R) (Q : Prescription (Press.portDeck G))
        (orders : ManuscriptQLocalScalarDirections.PaidOrders schedule schedule R.kit)
        (table : WilsonScalarSourceTableForecast.Paid schedule schedule R.kit)
        (booking : QLocalRequestedSectorCalendar.Paid J
          (WilsonGaussianDeterminantTender.joined G J χ (WilsonCoherentMayerCovarianceCalendar.decal G))
          extra γ R.kit),
        prediction R.kit ∧
        WilsonRootedPhysicalSpringReportedMS.Settled.{u} simple ε J extra γ M S R T W affine Q ∧
        WilsonRootedPhysicalSpringStoredMS.Ready simple M R affine Q orders ∧
        WilsonRootedPhysicalSpringUnitMS.Ready simple M R affine Q table ∧
        WilsonGaussianDeterminantQuarticMS.Common simple R J χ extra γ M Q affine orders booking ∧
        WilsonRootedPhysicalSpringAccurateMS.Ready simple M R affine Q table ∧
        WilsonGaussianSourceMS.Common simple R J χ extra γ M Q affine table booking := by
  let δ := WilsonCoherentMayerCovarianceCalendar.decal G
  let programme := WilsonGaussianDeterminantTender.joined G J χ δ
  let joint := @FundedPredictionSupply.Both G (@QLocalRequestedSectorCalendar.Paid G V J programme extra γ) (@prediction)
  obtain ⟨N,M,S,clock,matched,R,T,W,affine,Q,orders,table,⟨booking,receipt⟩,settled,stored,unit,accurate⟩ :=
    WilsonRootedPhysicalSpringAccurateMS.purchasedWith.{u} simple hε J extra γ hγ calendar dial (@joint)
      (fun s t => FundedPredictionSupply.both
        (QLocalRequestedSectorCalendar.prepaid J programme extra γ simple hγ s (ThroughLaunch.raging s t))
        (price s t))
  have fourth : WilsonGaussianDeterminantQuarticMS.Common simple R J χ extra γ M Q affine orders booking := WilsonGaussianDeterminantQuarticMS.common simple R J χ extra γ M Q affine orders booking stored
  have uniform : WilsonGaussianDeterminantUniformMS.Common simple R J χ extra γ M Q affine table booking := WilsonGaussianDeterminantUniformMS.common simple R J χ extra γ M Q affine orders table
    booking fourth unit
  exact ⟨N,M,S,clock,matched,R,T,W,affine,Q,orders,table,booking,receipt,settled,stored,unit,fourth,accurate,
    WilsonGaussianSourceMS.common simple R J χ extra γ M Q affine orders table booking uniform accurate⟩

end YM.Integration.WilsonGaussianFundedMS
