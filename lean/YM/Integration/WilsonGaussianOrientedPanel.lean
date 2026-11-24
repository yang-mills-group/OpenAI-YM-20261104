import YM.Integration.WilsonGaussianFiledPanel
import YM.Integration.WilsonMatrixOriginalOrientedPanel

/-! The calibrated signed physical panel, the complete local Gaussian Wick expansion, and the separated-product account are purchased on one original Wilson run. -/
noncomputable section
set_option autoImplicit false

namespace YM.Integration.WilsonGaussianOrientedPanel
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


/-- The same two marked fields have a strictly positive, once-oriented measured covariance on the
original reporting lens. Their incoming charges are bounded at every eligible cutoff and period. -/
def Measured {G : Gauge} (R : Run G) (simple : G.Simple) (Z : WilsonPrescription G) : Prop :=
  ∀ (B : ℕ), 0 < B → ∀ v : Extraction.Order,
    ∃ (w : Extraction.Order) (S : Table R.family.book)
      (F : Spec.Final R.family (v.refine w) S) (H : (Climb.Bel R.family.book).Hierarchy)
      (J : ℝ → PhysMS.tower S) (L : RG17.Layout F),
      PhysMS.Leading F J ∧ (∀ d : ℕ, ∀ᶠ r in Trace.Pilot.trail, PhysMS.Frame.obedient F H (J r) d) ∧
      L.level = WilsonMeasuredWindow.stop R.family.path.levels simple B ∧ L.lens ≤ (v.refine w).fuse ∧
      WilsonMatrixOriginalOrientedPanel.Observation F J Z H L

theorem measured {G : Gauge} {R : Run G} {T : Campaign R} (W : Campaign.Pillars R T)
    (simple : G.Simple) {ρ : ℝ} (funded : FundedOriginalProperties.{u} simple ρ W)
    (pace : WilsonWindowReportingPace.Slow R.kit) (Z : WilsonPrescription G) : Measured R simple Z := by
  exact fun _ hB v => WilsonMatrixOriginalOrientedPanel.on_run simple W funded pace Z hB v

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
        Measured R simple N ∧ WilsonWindowReportingPace.Slow R.kit ∧ WilsonReportColumnSubsidy.Eligible R.kit ∧
        PhysicalNext.Repeat.Legato.Citizen R.family R.w
          (PhysicalNext.Repeat.Legato.Bandage.mutt R.family.path.levels R.Q) R.doors ∧
        WilsonRootedPhysicalSpringReportedMS.Settled.{u} simple ε J extra γ M S R T W affine Q ∧
        WilsonRootedPhysicalSpringStoredMS.Ready simple M R affine Q orders ∧
        WilsonRootedPhysicalSpringUnitMS.Ready simple M R affine Q table ∧
        WilsonGaussianDeterminantQuarticMS.Common simple R J χ extra γ M Q affine orders booking ∧
        WilsonRootedPhysicalSpringAccurateMS.Ready simple M R affine Q table ∧
        WilsonGaussianSourceMS.Common simple R J χ extra γ M Q affine table booking := by
  obtain ⟨N,M,S,clock,matched,R,T,W,affine,Q,orders,table,booking,_,slow,subsidy,citizen,settled,remaining⟩ :=
    WilsonGaussianFiledPanel.purchased.{u} simple hε J χ extra γ hγ calendar dial
  exact ⟨N,M,S,clock,matched,R,T,W,affine,Q,orders,table,booking,
    measured W simple settled.1.original slow N,slow,subsidy,citizen,settled,remaining⟩

end YM.Integration.WilsonGaussianOrientedPanel
