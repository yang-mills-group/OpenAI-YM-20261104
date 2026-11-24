import YM.Integration.WilsonOriginalCensusDatedMaterial
import YM.Integration.WilsonNeutralTwoPrintPathDatedCensus

/-! The lower pupil uses the filed, fixed itinerary. Its single-side winding
is separated from the cofinal repeated input which enters the upper pupil. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusDatedSheets
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

def sideValue (physical:Bool)(s:(Stock.census (Fin n)).Mode)(d:ℕ)(u:Link G side):ℂ:=
  sheet R κ pt B x N b i e cells seed H.pin H.root H.source H.frill physical s d u

def winding (s:(Stock.census (Fin n)).Mode)(d:ℕ)(p:Bool):MvPolynomial (Woods G side) ℝ:=
  entry R κ pt B x N b i e cells seed H.pin H.root H.source H.frill s d p

theorem original (matched:∀y J,Same e (output H.prior J N y) (fixed R k κ pt N b i cells seed y J))
    {p':Passport side (Fin n)}{μ:Type}
    (low:μ → Row p' (Stock.census (Fin n)) G (Affinity.Wallet (room (Fin n))))
    (placed:p'=P)(names:μ=((z:I)×(words H z).Roster))(ink:HEq low (mounts H))
    {w:Fin n → ℝ}{σ₀ expense:ℝ}{order seats shelf:ℕ}
    (paid:Scene.Armada low w k σ₀ expense order seats shelf)(width:0 < σ₀)
    (layout:Layout G)(tape:Finset Age)(s:Hot (Stock.census (Fin n)))(d:ℕ)(through:d ≤ e)(u:Link G side):
    (peek dvd_rfl low k layout tape x d u).part s.val=sideValue H κ pt b cells seed x false s.val d u ∧
    ∀p,phase p (sideValue H κ pt b cells seed x true s.val d u)-phase p ((peek dvd_rfl low k layout tape x d u).part s.val)=
      MvPolynomial.eval u (winding H κ pt b cells seed x s.val d p):=by
  have lowread:=WilsonNeutralTwoPrintPathDatedCensus.printed R H.realm H.start H.paid κ pt N b cells seed
    H.prior H.nonneg H.lower H.radius.le matched B H.pin H.included H.marked H.positive H.root H.source H.frill
    (words H) (fun _=>rfl) low placed names ink paid width H.radius H.closed H.tickets x layout tape s d through u
  refine ⟨lowread,?_⟩
  intro p
  rw [lowread]
  exact WilsonNeutralTwoPrintPathDatedPolynomial.filed R κ pt B x N b i e cells seed H.pin H.root H.source H.frill s.val d p u

end YM.Integration.WilsonOriginalCensusDatedSheets
end
