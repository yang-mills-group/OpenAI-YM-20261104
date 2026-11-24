import YM.Integration.WilsonOriginalCensusDatedSheets
import YM.Integration.WilsonOriginalDatedPathWindingHeld

/-! The physical-period remainder at a bounded held field is priced by the dated
incoming print itself. The receipt preserves each occupied subset of the selected mode. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusDatedWindingFare
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
variable {G:Gauge}{n:ℕ}{R:Run G}{N i e:ℕ}{k:Fin n → ℕ}{σ:ℝ}
  {side:Side}{P:Passport side (Fin n)}{I:Type}[Fintype I]{B:I → Binder P (Stock.census (Fin n))}
  (H:Material R N i e k σ B)
  (κ:(v:Fin n) → Knob (H.tests v))(pt:Fin n → Chamber)(b:ℕ)
  (cells:Digits R.family.path.levels (Fin n))(seed:(v:Fin n) → Choice R k v)
  (x:Affinity.Wallet (room (Fin n)))


open WilsonNeutralTwoPrintPathCalendar (spent)
open WilsonNeutralTwoPrintPathRankFare (tariff)
open WilsonOriginalCensusDatedSheets (winding)
open WilsonNeutralTwoPrintPathDatedWage
local notation "block" z:max => (B z).mode.val
local notation "ports" z:max => toe (block z) (H.pin z) (H.root z) (H.frill z)
local notation "older" => fixed R k κ pt N b (i+1) cells seed
local notation "scope" z:max d:max => mass k (block z)+d

def price (s:(Stock.census (Fin n)).Mode)(d:ℕ)(M:ℝ)(ν C:I→ℕ→ℝ):ℝ:=
  ∑z,if s=(B z).mode then ∑r∈range ((scope z d)+1),
    ((‖∏v∈(B z).mode.val,(x v).val‖*‖touch (H.source z) (block z)‖)*
      (tariff (Loc G 1) r (ν z r) (C z r)*catchW (ν z r/512) side))*M^r else 0

theorem original (s:(Stock.census (Fin n)).Mode)(d:ℕ)(Y:Link G side)(M:ℝ)
    (nn:0≤M)(held:∀z,‖Y z‖ ≤ M)(ν C:I→ℕ→ℝ)
    (fit:∀z,4*crestCard (ports z) (block z) < side.val)
    (sale:∀z r,r ≤ scope z d →
       0<ν z r ∧ MarkU (ports z) (block z)
          (spent R k N i e side older (ports z) (cells i) (block z) d r)
          ((fixed R k κ pt N b i cells seed (ports z) (block z)).2 d r) (ν z r) (C z r))
    (p:Bool):|MvPolynomial.eval Y (winding H κ pt b cells seed x s d p)| ≤ price H x s d M ν C:=by
  exact WilsonOriginalDatedPathWindingHeld.paid R κ pt B x N b i e cells seed H.pin H.root
    H.source H.frill s d p Y M nn held ν C H.marked fit sale

end YM.Integration.WilsonOriginalCensusDatedWindingFare
end
