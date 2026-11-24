import YM.Integration.WilsonNeutralTwoPrintPathQuoted
import YM.Integration.WilsonNeutralTwoPrintPathCopies

/-! The issued inherited group word against the independently prescribed finite
output on its actual input. The marked constant is the rank-zero summand. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
set_option maxHeartbeats 1200000
noncomputable section
namespace YM.Integration.WilsonNeutralTwoPrintPathPlaced
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
variable {G:Gauge}{n e j:ℕ}{k D:Fin n → ℕ}{S J:Finset (Fin n)}{A δ σ:ℝ}
variable (R:Run G)(Y:Realm G (e+1) Credit.leanC)(lo:Y.anchor ≤ j)(enrolled:Paid R Y lo D k δ σ)
variable (N:ℕ) (c:Fin n)(X:Input Y lo S k D A)(included:J⊆S)(pin:c∈J)(positive:0 ≤ A)
variable (older:j<N)(deep:0 < mass k J)(sw:0 ≤ σ)(o:Cover)(t:Case D)(u:Frill J c)
local notation "M₀" => R.family.path.levels.clock.hatBeta j^δ*A^J.card

open WilsonOlderFreshConnectedBirth WilsonCoeffUV.Blue WilsonCoeffUV.Bank.Mosaic.Near
open WilsonCoeffUV.Bank.Carp
local notation "T" => WilsonOlderFreshConnectedBirth.issued R Y lo enrolled N c X included pin positive older deep sw o t u
local notation "P₀" => packetH J (output X J N) (mass k J) (e+1) c o u

open WilsonOlderFreshConnectedBinding


open QuadraticLocal.Poetry QuadraticLocal.Sunrise QuadraticLocal.Sunrise.Aviary Stationary
open WilsonOriginalPrimerReceipts WilsonNeutralTwoPrintPathJet
open Primitives.TwoWave AllOrder.Haiku AllOrder.Ink Response PertExtension.Series

open WilsonNeutralTwoPrintPathRoll WilsonOlderFreshConnectedAssembly
open Further.PhysicalPeriodLimitF933 Macrame Shingle AllOrder.Ker FVA1Physical FVA1Physical.TwoReset


open WilsonCoeffUV.Winding WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Bank.Mosaic.Near
open WilsonNeutralTwoPrintPathRead
local notation "deposit" => output X J N (toe J c o u)
local notation "report" => relative Y lo N c X o t u

open private move_roll from YM.Integration.WilsonNeutralTwoPrintPathCopies

theorem original {n':Side}{pp:Passport n' Unit}{marks:Marker.Census Unit}(site:Binder pp marks)
    (actors:Unit→Set ℂ)(bounded:∀x,‖value actors x‖≤1)(x:Affinity.Wallet actors)
    (width:0<σ)(closed:Cloze D k Y Credit.leanC)(tickets:Insure n (mass k univ) Y Credit.leanC)
    (layout:Layout G)(tape:Finset Age)(h:ℕ)(through:h≤e)(B:Link G n'):
    (peek dvd_rfl ((T).rows site actors) (fun _=>mass k J) layout tape x h B).part (WilsonNeutralRenderedColumn.submitted site).val=
      value actors x*Complex.ofReal (diagonal (mass k J+h) (report h) (B ∘ jog site.center)):=by
  rw [WilsonThermometerPositionFilmSelf.pupil]
  have dose:=WilsonOriginalPrimerCourseRead.salary site (T).roll (T).fare σ (T).paid (T).legal (T).positive
    actors bounded x width
  have heard:=WilsonOriginalPrimerDischarge.filed site (T).roll (T).fare σ (T).paid (T).legal (T).positive
    (value actors) x width dose layout tape B h
  refine heard.trans ?_
  have allRows : (∑a:Fin (e+1),(((T).roll a).folded a.val h).table n' (mingle B (WilsonElectedPrimaryTensor.pin site.center)))=
      ∑a:Fin (e+1),(((T).roll a).folded a.val h).table n' (mingle (B ∘ jog site.center) (WilsonElectedPrimaryTensor.pin (0:Site n'))):=
    Finset.sum_congr rfl fun a _=>move_roll R Y lo enrolled N c X included pin positive older deep sw o t u
      a width h site.center B
  rw [allRows,WilsonNeutralTwoPrintPathRead.register R Y lo enrolled N c X included pin positive older deep sw o t u
    width closed tickets h through (B ∘ jog site.center)]


end YM.Integration.WilsonNeutralTwoPrintPathPlaced
end
