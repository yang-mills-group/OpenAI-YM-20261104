import YM.Integration.WilsonAddressedPublicFirstExtent
import YM.Integration.WilsonOriginalCensusCanonicalRelativePeriodSchedule
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonAddressedPublicFirstPeriod
open scoped Classical


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

open Comparison.Density.Transport Pert.Asymptotics
open WilsonReceivedCanonicalSocketSeed (present contact)
open WilsonOriginalCensusCanonicalSparseBudget (winding)
open WilsonOriginalCensusAngularFace (sides)
variable {G:Gauge}

variable (R:Run G)(simple:G.Simple){n:ℕ}
  (d lens:Fin n→ℕ)(pt:Fin n→Chamber)(charges:Fin n→ℕ)(tube:LinkTube G)
  (upperOrder lowerOrder target p:ℕ)

open WilsonAddressedPublicFirstExtent
open WilsonOriginalCensusCanonicalRelativePeriodSchedule (Appointment)
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open WilsonNeutralTwoPrintPathBoxHome (breadth)
open WilsonIndependentCollarOrbitalReception (relative)
variable {q:ℕ}
def appointment (seller:ℕ → Gear G → ℝ)(fund:FundedMarkedCoverRows.prices seller R.kit)
    (bought:2*(p+1)≤target):
    Appointment R simple d lens pt charges tube upperOrder lowerOrder target p bought:=
  WilsonOriginalCensusCanonicalRelativePeriodSchedule.original R simple d lens pt charges tube
    upperOrder lowerOrder target p seller fund bought

theorem original {bought:2*(p+1)≤target}
    (menu:Appointment R simple d lens pt charges tube upperOrder lowerOrder target p bought)
    (i:ℕ){V:Realm G (q+1) Credit.leanC}(ground:Fin n → Cover)(m a:ℕ):
    ∀ᶠ per:ℕ in atTop,
      menu.period i (extent V.draws ground m a)≤per ∧
      ∀ (cells:WilsonReceivedFixedDigitHistory.Digits V.draws (Fin n))(S:Finset (Fin n))(o:Fin n),
        breadth S o 0 (relative S o (WilsonReceivedChronologicalMaterialLine.homes cells ground m a))
          ≤ extent V.draws ground m a:=by
  filter_upwards [eventually_ge_atTop (menu.period i (extent V.draws ground m a))] with per late
  exact ⟨late,fun cells S o=>WilsonAddressedPublicFirstExtent.original cells ground m a S o⟩
end YM.Integration.WilsonAddressedPublicFirstPeriod
end
