import YM.Integration.WilsonOriginalCensusFaceSheet
import YM.Integration.WilsonOriginalCensusFaceCalendar

/-! The lower-board rate of a physical face uses only its declared
addresses, its signed test and the wallets of its occupied slots. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusFaceAdmission
open Function Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn
open QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Mentor Org
open AllOrder AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Transit WheelP
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Boulevard
open Push Push.PriceCompiler QuadraticLocal.Rebirth QuadraticLocal.Affinity ConnectedActivityE6
open AnalyticBridge VerifiedReset RemainderComparison LocalComparison Comparison.RG02
open WilsonOlderFreshGraphVote WilsonOlderFreshGraphArmada
open scoped Classical BigOperators Topology

open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Wheel.Express WilsonCoeffUV.Embroider
open WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Soil WilsonCoeffUV.Wheel.Flooring
open Work.F08
open scoped BigOperators Classical


open FundedMarkedPathSelection
open PhysicalNext.Repeat.Legato WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Embroider.Canvas
open ComparisonDensity.Address WilsonCoeffUV.Shard WilsonCoeffUV.Winding OriginalIssuedMarkedRows
open ActualRunAdmissionScales OriginalBareMarkedInvoice Filter Function
open WilsonOlderFreshConnectedRobe WilsonCoeffUV.Bank.Ticket
open scoped Topology

open WilsonOlderFreshConnectedRobe WilsonOlderFreshGraphSlate WilsonOlderFreshConnectedRoll
open WilsonOlderFreshConnectedPin WilsonOlderFreshConnectedAppointment FundedMarkedCoverRows
open WilsonCoeffUV.Bank.Ticket

open WilsonOlderFreshConnectedBirth WilsonCoeffUV.Blue WilsonCoeffUV.Bank.Mosaic.Near
open WilsonCoeffUV.Bank.Carp
open WilsonOlderFreshConnectedBinding


open QuadraticLocal.Poetry QuadraticLocal.Sunrise QuadraticLocal.Sunrise.Aviary Stationary
open WilsonOriginalPrimerReceipts WilsonNeutralTwoPrintPathJet
open Primitives.TwoWave AllOrder.Haiku AllOrder.Ink Response PertExtension.Series

open WilsonNeutralTwoPrintPathRoll WilsonOlderFreshConnectedAssembly
open Further.PhysicalPeriodLimitF933 Macrame Shingle AllOrder.Ker FVA1Physical FVA1Physical.TwoReset


open WilsonCoeffUV.Winding WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Bank.Mosaic.Near
open WilsonNeutralTwoPrintPathRead

open WilsonNeutralTwoPrintPathFixed (parcel)
open WilsonReceivedFixedDigitHistory (Digits)
open WilsonReceivedFixedDigitCanonical (fixed)
open OriginalMarkedSourceComet WilsonThermometerDeclaredSeeds
open WilsonNeutralTwoPrintPathQuoted (bill)

open WilsonOriginalMixedBlockRows WilsonRegisteredPairUnaryWallet Multi
open WilsonNeutralTwoPrintPathCensus (slates)
open WilsonNeutralTwoPrintPathDatedPolynomial (row sheet entry)
open WilsonReceivedCoverGrade (Same)
open FundedMarkedPathSelection (output)

open WilsonOriginalCensusDatedMaterial (Material words mounts)
open WilsonCapturedRootedAngularSlots WilsonCapturedPrimaryWindingMaterialRead WilsonNeutralTwoPrintPeg
open WilsonNeutralTwoPrintPathPolynomial RegulatorIR.Diagram

open WilsonOriginalCensusFaceSites (binder port pin frill root)
open WilsonOriginalCensusDatedSheets (sideValue)
open WilsonNeutralTwoPrintPathCalendar (spent)
open WilsonReceivedCompactVerseEntrance (submit)
variable {G:Gauge}{n:ℕ}{R:Run G}{N i e:ℕ}{k:Fin n→ℕ}{σ:ℝ}{side:Side}
local notation "J" => Stock.census (Fin n)
local notation "I" => Hot (J)
variable (y:Fin n → Cover)(L:Material R N i e k σ (binder side y))(test:Case L.tests)


open WilsonOriginalCensusFaceSheet (Addressed)
open WilsonOriginalCensusDatedHeldTariff (salary)
open WilsonCoeffUV.Winding

theorem extent {s:I}{v z:Fin n → Cover}(same:∀j∈s.val.val,v j=z j):
    crestCard v s.val.val=crestCard z s.val.val:=by
  have h:(fun a:s.val.val=>v a.val)=(fun a:s.val.val=>z a.val):=
    funext (fun a=>same a.val a.property)
  exact congrArg (league Bank.terrain) h

def housed (R:Run G)(i per:ℕ):Prop:=∀grid:Side,(R.family.side i per).val ∣ grid.val →
    ∀s:I,4*crestCard y s.val.val < grid.val

theorem housing (R:Run G)(i:ℕ):∀ᶠ per in atTop,housed y R i per:=by
  filter_upwards [WilsonOriginalCensusFaceCalendar.housing y R i] with per sale
  intro grid divides s
  simpa only [extent (s:=s) (WilsonOriginalCensusFaceSites.source y s)] using sale grid divides s

theorem fit (A:Addressed y L test){per:ℕ}(geometry:housed y R i per)(tiles:(R.family.side i per).val ∣ side.val)
    (s:I):4*crestCard (toe s.val.val (L.pin s) (L.root s) (L.frill s)) s.val.val < side.val:=by
  rw [extent (A.agrees s)]
  exact geometry side tiles s

theorem price (A:Addressed y L test)(x:Affinity.Wallet (room (Fin n)))(s:I):
    salary L x s.val=‖∏v∈s.val.val,(x v).val‖*‖touch test s.val.val‖:=by
  change (∑z:I,if s.val=z.val then ‖∏v∈z.val.val,(x v).val‖*‖touch (L.source z) z.val.val‖ else 0)=_
  rw [sum_eq_single s]
  · simp [A.ink]
  · intro z _ different
    exact if_neg (fun eq=>different (Subtype.ext eq).symm)
  · simp

theorem collar (R:Run G)(days:Finset ℕ)(site:ℕ → Fin n → Cover):
    ∀ᶠ per in atTop,∀j∈days,housed (site j) R j per:=by
  exact (eventually_all_finset days).2 (fun j _=>housing (site j) R j)

end YM.Integration.WilsonOriginalCensusFaceAdmission
end
