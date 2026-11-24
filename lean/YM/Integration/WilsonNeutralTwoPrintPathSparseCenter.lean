import YM.Integration.WilsonOriginalCensusFaceSheet
import YM.Integration.WilsonOriginalCensusFixedBank

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonNeutralTwoPrintPathSparseCenter
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

variable (κ:(v:Fin n)→Knob (L.tests v))(pt:Fin n→Chamber)(b:ℕ)
  (cells:Digits R.family.path.levels (Fin n))(seed:(v:Fin n)→Choice R k v)
  (x:Affinity.Wallet (room (Fin n)))
local notation "previous" => fixed R k κ pt N b (i+1) cells seed


/-- The before-cutoff prior selected for this material pays both the compact
entrance and the physical single-sheet reading, including its signed constant. -/
theorem original (active:WilsonOriginalCensusFaceSheet.Addressed y L test)
    (income:WilsonOriginalCensusFixedBank.Income (k:=k) R κ pt e i)(later:i<b)(live:b≤N)
    (written:∀z s,output L.prior s N z=fixed R k κ pt N b i cells seed z s) :
    Wellness k (submit (previous) k e) ∧
    (∀z s,Same e (output L.prior s N z) (fixed R k κ pt N b i cells seed z s)) ∧
    ∀(s:I)(h:ℕ)(Y:Link G side),sideValue L κ pt b cells seed x true s.val h Y =
      (∏v∈s.val.val,(x v).val)*Complex.ofReal (diagonal (mass k s.val.val+h)
        (fun r z=>(touch test s.val.val) (spent R k N i e side (previous) y (cells i) s.val.val h r z)) Y):=by
  obtain ⟨σ,A,warm,one,earned⟩:=income b later
  obtain ⟨well,bill⟩:=earned N live cells seed
  have paid:=(WilsonReceivedCompactVerseEntrance.original (previous) well warm one bill).2.1
  refine ⟨paid,?_,fun s h Y=>WilsonOriginalCensusFaceSheet.original y L test κ pt b cells seed x active paid s h Y⟩
  intro z s
  rw [written z s]
  exact fun _ _=>rfl

end YM.Integration.WilsonNeutralTwoPrintPathSparseCenter
end
