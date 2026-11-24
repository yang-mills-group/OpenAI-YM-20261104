import YM.Integration.WilsonOriginalCensusCanonicalRegulatorMenu
import YM.Integration.WilsonIndependentCollarCanonicalRelativeMenu
/-! The separately chosen period starts after an activated report and its physical support bound. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusCanonicalRelativePeriodSchedule
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
local notation "peak" => 3*WilsonOriginalFullRosterBookedHearing.roof d d charges target
local notation "rank" => WilsonOriginalCensusPhysicalLoad.rank (sides d d)
local notation "start" b:max => WilsonOriginalCensusSparseRosterOpening.first R simple tube d d charges upperOrder lowerOrder target p b


structure Appointment (bought:2*(p+1)≤target) where
  first : ℕ
  period : ℕ→ℕ→ℕ
  late : ∀i,first ≤ i→(start bought) ≤ i
  jets : ∀i,first ≤ i→∀N per,i<N→∀w≤p,((R.family.path.levels.clock.hatBeta i)^p)⁻¹≤(regulatorRun R.family N per (i+1))^w
  funds : ∀i,first ≤ i→∀breadth per,period i breadth≤per→WilsonIndependentCollarCanonicalRelativeMenu.Paid R d
    (fun v=>contact (lens v)) pt (peak) breadth (present lens) (winding (R.family.path.levels.clock.hatBeta i) p (rank)) i per

/-- The report gate and its later physical period are chosen before any microscopic cutoff or post. -/
def original (seller:ℕ→Gear G→ℝ)(fund:FundedMarkedCoverRows.prices seller R.kit)(bought:2*(p+1)≤target):
    Appointment R simple d lens pt charges tube upperOrder lowerOrder target p bought:=by
  have witness:∀ᶠ i:ℕ in atTop, (start bought) ≤ i ∧
      (∀N per,i<N→∀w≤p,((R.family.path.levels.clock.hatBeta i)^p)⁻¹≤(regulatorRun R.family N per (i+1))^w) ∧
      ∀breadth,∀ᶠ per:ℕ in atTop,WilsonIndependentCollarCanonicalRelativeMenu.Paid R d (fun v=>contact (lens v)) pt
        (peak) breadth (present lens) (winding (R.family.path.levels.clock.hatBeta i) p (rank)) i per:=by
    filter_upwards [WilsonOriginalCensusCanonicalRegulatorMenu.original R simple d lens pt charges tube upperOrder lowerOrder target p seller fund bought,
      WilsonIndependentCollarCanonicalRelativeMenu.original R d (fun v=>contact (lens v)) pt simple seller fund (peak)]
        with i measured earned
    refine ⟨measured.1,measured.2.1,fun b=>?_⟩
    have hh:0<R.family.path.levels.clock.hatBeta i:=zero_lt_one.trans (R.alloy.B.a.fits.delayed i)
    apply earned b (present lens) _
    unfold winding
    positivity
  let opening:=eventually_atTop.mp witness
  let first:=opening.choose
  let after (i:ℕ)(live:first ≤ i)(b:ℕ):=(eventually_atTop.mp ((opening.choose_spec i live).2.2 b))
  let period (i b:ℕ):=if hi:first ≤ i then (after i hi b).choose else 0
  refine ⟨first,period,fun i live=>(opening.choose_spec i live).1,fun i live=>(opening.choose_spec i live).2.1,?_⟩
  intro i live breadth per due
  apply (after i live breadth).choose_spec per
  simpa only [period,dif_pos live] using due

end YM.Integration.WilsonOriginalCensusCanonicalRelativePeriodSchedule
end
