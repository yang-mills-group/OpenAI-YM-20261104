import YM.Integration.WilsonOriginalCensusCanonicalAngularMenu

open scoped Classical
noncomputable section
namespace YM.Integration.WilsonIndependentCollarCanonicalPeriodGrant
open Work.F08 WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.Express WilsonCoeffUV.Wheel.Cadenza
open Function Filter Finset Lattice Wilson RG Precision Laurent WilsonCoeffUV Tree Bloch Exterior
open Next.Foundations PhysicalNext.Repeat.Legato
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer
open WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Bank.Realm
open WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Mosaic.Near WilsonCoeffUV.Blue WilsonCoeffUV.Soil
open WilsonCoeffUV.Embroider WilsonCoeffUV.Winding WilsonCoeffUV.Bank.Ticket
open WilsonReceivedDatedVerseReprint WilsonReceivedCompactVerseEntrance
open WilsonMarkedIndependentPhysicalIntake WilsonMarkedIndependentMixedGeometry
open AnalyticNext.QuarticMatch.Sheets IndependentSourcePathFamily
open scoped Classical BigOperators
variable {G:Gauge}{I:Type}[Fintype I][DecidableEq I]{D k:I→ℕ}{e:ℕ}

open Further.PhysicalPeriodLimitF933 Macrame Shingle FVA1Physical TwoReset
open WilsonOriginalRelativePageTail (retained)
open WilsonPointChildRelativeLift (centers)
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Bank.Mosaic.Near WilsonCoeffUV.Blue
open WilsonNeutralTwoPrintPathPageLedger (price)
open WilsonNeutralTwoPrintPathRankFare (tariff)
open WilsonCoeffUV.Bank.Carp (plume)


open WilsonOriginalCensusOrbitCenters (layout shifted)
open WilsonOriginalConnectedPeriodPage (Deck)
open WilsonOriginalCensusDeckMean (mean)
open WilsonNeutralTwoPrintPathPageSeason (high)

open WilsonReceivedFixedDigitIntake (next)
open WilsonCoeffUV.Wheel.Motion (steppedC ramble)
open private translated from YM.Integration.WilsonPointChildCenteredSeat

open WilsonNeutralTwoPrintPathStart (returned)
open WilsonReceivedFixedDigitCanonical (fixed)
open WilsonReceivedFixedDigitHistory (Digits)
open WilsonNeutralTwoPrintPathBoxMean (plotted)
open WilsonThermometerDeclaredSeeds
open OriginalMarkedSourceComet
open scoped Topology
variable (R:Run G)(k:I→ℕ)(κ:(v:I)→Knob (D v))(pt:I→Chamber)

open WilsonOriginalCensusCanonicalPeriod (Actual Covered)
open WilsonOriginalCensusCanonicalOpening (copyRead central)
open WilsonNeutralTwoPrintPathBoxHome (breadth)
open WilsonNeutralTwoPrintPathBoxInk (ink)
open WilsonNeutralTwoPrintPathBoxPlacement (homes)
open scoped Classical BigOperators Topology

open WilsonNeutralTwoPrintPathJet (diagonal)
open WilsonIndependentCollarOrbitalReception (relative at_front)
open WilsonOriginalRawQReversion (coordinates)

open WilsonOriginalCensusCanonicalAngularSum (weight)


open WilsonOriginalCensusCanonicalAngularMenu (repeated plottedLow)

/-- The one period opening on the physical board for the canonical seed and test. -/
def Paid (Q i per breadthCap:ℕ)(t:Case D)(ε:ℝ):Prop:=
  ∀N,i<N → ∀(seed:(v:I)→Choice R k v)(cells:Digits R.family.path.levels I)
    (y:I → Cover)(S:Finset I)(o:I),o∈S → breadth S o (y o) (relative S o y)≤breadthCap →
    ∀a,a≤Q → ∀(Y:Stationary.Link G (R.family.side i per)),‖Y‖≤1 → ∀c:ℂ,
    let f:=repeated R k κ pt N i seed cells (R.family.side i per) y S o a t Y c
    ‖limUnder (coverFilter R.family.path.levels.S i (R.family.side i per)) f-
      plottedLow R k κ pt N i seed cells (R.family.side i per) y S a t Y c‖≤‖c‖*ε

theorem original (simple:G.Simple)(sale:ℕ→Gear G→ℝ)(paid:FundedMarkedCoverRows.prices sale R.kit)(Q:ℕ):
    ∀ᶠ i:ℕ in atTop,∀b(t:Case D)(ε:ℝ),0<ε → ∀ᶠ per:ℕ in atTop,Paid R k κ pt Q i per b t ε:=by
  filter_upwards [WilsonOriginalCensusCanonicalAngularMenu.original R k κ pt simple sale paid Q] with i d
  intro b t ε hp
  filter_upwards [d b t ε hp] with per h
  intro N hn seed cells y S o ho near a ha Y unit c
  exact (h N hn seed cells (R.family.side i per) dvd_rfl y S o ho near a ha Y unit c).2

end YM.Integration.WilsonIndependentCollarCanonicalPeriodGrant
end

