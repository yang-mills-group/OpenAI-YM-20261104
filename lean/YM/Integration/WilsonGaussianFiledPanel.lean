import YM.Integration.WilsonGaussianCitizenMS
import YM.Integration.WilsonMatrixOriginalFundedPanel

/-! The calibrated signed physical panel, the complete local Gaussian Wick expansion, and the separated-product account are purchased on one original Wilson run. -/
noncomputable section
set_option autoImplicit false

namespace YM.Integration.WilsonGaussianFiledPanel
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


open private column_prices from YM.Integration.WilsonGaussianCitizenMS

/-- The original RG16 delay is bought before the skeleton has selected any period. -/
private theorem slow_prices {G : Gauge} (simple : G.Simple) :
    FundedPredictionSupply.AllPrices (@WilsonWindowReportingPace.Slow G) := by
  intro s t targets expenses chart programs wages baton fees
  refine ⟨0, ?_⟩
  intro l hl D w U Z post scouts θ stages cost V quarter
  obtain ⟨W,hVW,grant⟩ := RG16.later D simple V (fun _ => 0)
  refine ⟨W,hVW,?_⟩
  intro Y hY bar wait priced B
  dsimp only
  intro η q exchange menu aux rider booth sheltered works divides
  obtain ⟨plenty,pace⟩ := grant Y hY wait B.a B.valid
  exact ⟨plenty, fun m => (le_max_left _ _).trans (pace m)⟩

/-- The same two marked fields have a nonzero observed signed covariance on the
original reporting lens. Their incoming charges are bounded at every eligible cutoff and period. -/
def Measured {G : Gauge} (R : Run G) (simple : G.Simple) (Z : WilsonPrescription G) : Prop :=
  ∀ (B : ℕ), 0 < B → ∀ v : Extraction.Order,
    ∃ (w : Extraction.Order) (S : Table R.family.book)
      (F : Spec.Final R.family (v.refine w) S) (H : (Climb.Bel R.family.book).Hierarchy)
      (J : ℝ → PhysMS.tower S) (L : RG17.Layout F),
      PhysMS.Leading F J ∧ (∀ d : ℕ, ∀ᶠ r in Trace.Pilot.trail, PhysMS.Frame.obedient F H (J r) d) ∧
      L.level = WilsonMeasuredWindow.stop R.family.path.levels simple B ∧ L.lens ≤ (v.refine w).fuse ∧
      WilsonMatrixOriginalFundedPanel.Observation F J Z H L

theorem measured {G : Gauge} {R : Run G} {T : Campaign R} (W : Campaign.Pillars R T)
    (simple : G.Simple) {ρ : ℝ} (funded : FundedOriginalProperties.{u} simple ρ W)
    (pace : WilsonWindowReportingPace.Slow R.kit) (Z : WilsonPrescription G) : Measured R simple Z := by
  intro B hB v
  obtain ⟨w,S,F,H,arch,l,J,A,δ,u₀,bank,L,bliss,lead,obey,same,centered,cal,coupling,pegs,level,lens,seen⟩ :=
    WilsonMatrixOriginalFundedPanel.on_run simple W funded pace Z hB v
  exact ⟨w,S,F,H,J,L,lead,obey,level,lens,seen⟩

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
  let joint : Prediction G := FundedPredictionSupply.Both (@WilsonWindowReportingPace.Slow G) (@WilsonReportColumnSubsidy.Eligible G)
  obtain ⟨N,M,S,clock,matched,R,T,W,affine,Q,orders,table,booking,subsidy,settled,remaining⟩ :=
    WilsonGaussianFundedMS.purchasedWith.{u} simple hε J χ extra γ hγ calendar dial
      (@joint) (fun s t => FundedPredictionSupply.both (slow_prices simple s t) (column_prices s t))
  have citizen := WilsonInvariantActionCaptureRun.on_run simple W settled.1.original subsidy.2
  exact ⟨N,M,S,clock,matched,R,T,W,affine,Q,orders,table,booking,measured W simple settled.1.original subsidy.1 N,subsidy.1,subsidy.2,citizen,settled,remaining⟩

end YM.Integration.WilsonGaussianFiledPanel
