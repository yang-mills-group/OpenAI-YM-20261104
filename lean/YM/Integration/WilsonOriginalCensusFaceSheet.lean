import YM.Integration.WilsonOriginalCensusFaceSites
import YM.Integration.WilsonOriginalCensusFaceMist
import YM.Integration.WilsonOriginalCensusDatedSheets

/-! The genuine dated retained pupil at one common array on every physical
face. Each occupied label uses its own original coordinate and calibration. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusFaceSheet
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

structure Addressed:Prop where
  ink (s:I):L.source s=test
  center (s:I):wrap side (L.root s)=(binder side y s).center
  agrees (s:I)(v:Fin n):v∈s.val.val →
    toe s.val.val (L.pin s) (L.root s) (L.frill s) v=y v

theorem recenter {side:Side}(A:Gen ℝ (Woods G side))(w:ℕ)(u:Site side)(Y:Link G side):
    diagonal w (fun r a=>A r (jog u ∘ a)) (Y ∘ jog u)=diagonal w A Y:=by
  simp only [diagonal,Blue.toll]
  apply sum_congr rfl
  intro r _
  exact Fintype.sum_equiv (Equiv.piCongrRight fun _:Fin r=>jog u) _ _ (fun _=>rfl)

variable (κ:(v:Fin n)→Knob (L.tests v))(pt:Fin n→Chamber)(b:ℕ)
  (cells:Digits R.family.path.levels (Fin n))(seed:(v:Fin n)→Choice R k v)
  (x:Affinity.Wallet (room (Fin n)))
local notation "previous" => fixed R k κ pt N b (i+1) cells seed

theorem original (active:Addressed y L test)(filed:Wellness k (submit (previous) k e))
    (s:I)(h:ℕ)(Y:Link G side):
    sideValue L κ pt b cells seed x true s.val h Y =
      (∏v∈s.val.val,(x v).val)*Complex.ofReal (diagonal (mass k s.val.val+h)
        (fun r z=>(touch test s.val.val) (spent R k N i e side (previous) y (cells i) s.val.val h r z)) Y):=by
  unfold sideValue WilsonNeutralTwoPrintPathDatedPolynomial.sheet
  rw [sum_eq_single s]
  · rw [if_pos (show s.val=(binder side y s).mode from rfl)]
    unfold WilsonNeutralTwoPrintPathDatedPolynomial.row
    simp only [if_true]
    rw [active.ink s,active.center s]
    change (∏v∈s.val.val,(x v).val)*Complex.ofReal (diagonal (mass k s.val.val+h)
      (fun r z=>(touch test s.val.val) (spent R k N i e side (previous)
        (toe s.val.val (L.pin s) (L.root s) (L.frill s)) (cells i) s.val.val h r
        (jog (binder side y s).center ∘ z))) (Y ∘ jog (binder side y s).center))=_
    rw [WilsonOriginalCensusFaceMist.response R k N i e side (previous) filed _ y
      (cells i) s.val.val (active.agrees s)]
    exact congrArg (fun z:ℝ=>(∏v∈s.val.val,(x v).val)*Complex.ofReal z)
      (recenter (fun r z=>(touch test s.val.val) (spent R k N i e side (previous) y (cells i) s.val.val h r z))
        (mass k s.val.val+h) (binder side y s).center Y)
  · intro t _ different
    exact if_neg (fun equal=>different (Subtype.ext equal.symm))
  · simp

end YM.Integration.WilsonOriginalCensusFaceSheet
end
