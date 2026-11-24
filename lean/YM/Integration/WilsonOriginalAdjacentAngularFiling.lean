import YM.Integration.WilsonOriginalCensusAngularFace
import YM.Integration.WilsonOriginalRestampedCensusFiling
import YM.Integration.WilsonOriginalCensusRestamp
import YM.Integration.WilsonOriginalDepositedCensusBook
import YM.Integration.WilsonOriginalAdjacentCensusFiling
import YM.Integration.WilsonOriginalCensusMount
import YM.Integration.WilsonOriginalFreshJoinedRows
import YM.Integration.WilsonOriginalFreshPrintedGross

/-! Mount the three genuine programs from two adjacent original Wilson posts on a
single optical slice. The signed words read the unmasked output of the upper post
and the incoming independently submitted program of the next lower post. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalAdjacentAngularFiling
open Function Finset Filter MeasureTheory Lattice Wilson RG Tree Marker QuadraticLocal Ac Source Labels
open QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Mentor QuadraticLocal.Affinity
open Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato AllOrder.Transit.WheelP
open AnalyticBridge VerifiedReset RemainderComparison Push Push.PriceCompiler Push.AbsoluteSums
open Stationary Comparison.RG02 QuadraticLocal.Rebirth VowsR LocalComparison ConnectedActivityE6
open OPE.Therm Multi WilsonRootedKioskOccupiedSlip WilsonOriginalSeparatedRegular
open WilsonOriginalSeparatedMask Comparison.Density.Transport
open scoped BigOperators Classical
variable {G:Gauge} (R:Run G) (simple:G.Simple) {m j N per k:ℕ}
  (hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q:D.Tab R.rolls)
  (π:ℕ → Layout G) (Γ:ℕ → Pace.Coin) (Ψ:∀i,RG.Rep G (R.family.side i per))
  (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  {φ:ℕ → ℕ}(books:Mentor.Offices.Books D R.rolls Q φ) (lo:m ≤ j) (cut:j+1 < N)
  (ahead:Mentor.Forecast D R.rolls Q φ books)
  {V:Type} [Fintype V] [DecidableEq V] {X Y:V→Type}
  [∀v,AddCommGroup (X v)] [∀v,Module ℝ (X v)] [∀v,AddCommGroup (Y v)] [∀v,Module ℝ (Y v)]
  (A:∀v,Set (X v)) (K:∀v,Submodule ℝ (X v)) (A':∀v,Set (Y v)) (K':∀v,Submodule ℝ (Y v))
  (grades grades':V→ℕ)(order shelf seats order' shelf' seats':ℕ)
  (upperLaw:Wallet A → Config G (R.family.side ((j+1)+1) per) → Poly (Stock.census V))
  (lowerLaw:Wallet A' → Config G (R.family.side (j+1) per) → Poly (Stock.census V))
  (high:WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead A K grades order shelf
    seats (j+1) (Nat.le_succ_of_le lo) upperLaw)
  (low:WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead A' K' grades' order' shelf' seats' j lo lowerLaw)
local notation "vac" => Ψ (j+1)
local notation "marks" => Stock.census V
local notation "student" => Oak.student (n:=per) R hk D Q π Γ books (Nat.le_succ_of_le lo)
  high.op high.lesson ahead A high.model order high.voter
local notation "Lu" => rendered (student) (vac).p (Coat.gStep (Ψ ((j+1)+1)).beta)
local notation "next" => rendered low.model (vac).p (Coat.gStep (vac).beta)
local notation "home" => (high.passport.coarser (R.family.path.levels.clock.op (j+1) per).ratio).origin
variable {tariff tariff':(Stock.census V).Mode→ℝ}
  (highBook:WilsonOriginalCensusAppointment.Book R hk D Q π Γ Ψ books (Nat.le_succ_of_le lo) ahead
    A K grades order shelf seats upperLaw high tariff)
  (lowBook:WilsonOriginalCensusAppointment.Book R hk D Q π Γ Ψ books lo ahead
    A' K' grades' order' shelf' seats' lowerLaw low tariff')


local notation "ζ" => Oak.grade0 R hk D Q π Γ (Nat.le_succ_of_le lo) high.lesson
local notation "gf" => Coat.gStep (Ψ ((j+1)+1)).beta
local notation "gc" => Coat.gStep (vac).beta
local notation "stamped" => Mutation.stamp (student) (Γ (j+1)) (ζ) (Burn.horizon k+2) order
local notation "carried" => Mutation.grow (student) (Γ (j+1)) (ζ) (Burn.horizon k+2) order
  (gf) (gc) (vac) high.output
local notation "L" => rendered (stamped) (vac).p (gc)
local notation "Ω" => Oak.expenseReal R hk D Q π Γ books (Nat.le_succ_of_le lo) high.op high.lesson ahead order shelf
local notation "w₂" => Stoop.radius high.w ((Ω)^6)

open WilsonOriginalCensusAngularFace
local notation "σ" => Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (j+1))
local notation "fig" => Oak.figureReal R hk D Q π Γ books (Nat.le_succ_of_le lo) high.op high.lesson ahead order shelf
local notation "both" => roster (stamped) low.model
local notation "wages" => sides (w₂) low.w
local notation "costs" => sides (budgetR R (j+1)) low.cost
local notation "degrees" => sides grades grades'
local notation "orders" => sides order order'
local notation "loads" => sides high.op.count low.op.count
local notation "shelves" => sides shelf shelf'
include simple course cut in
def original (way:WayStation R.kit)(pass:Pass D Q R.alloy R.kit)(month:Scholar.Month R.rolls D Q R.alloy.delay)
    (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (fits:order ≤ Burn.horizon k+1)(narrow:shelf ≤ R.alloy.B.a.clock.J (j+1))
    (load:high.op.count ≤ Burn.horizon k+2)(q:ℕ)(deep:2*q+8 ≤ order)(aged:q+3 ≤ 3*k+2){ε:ℝ}(ep:0<ε)
    (late:WilsonReceivedMeasuredStampPrice.opening R simple q order k deep aged ep ≤ j+1)
    (warm:Spill.Raffle.Warm G D R.alloy.delay φ)(depth:order' ≤ R.alloy.B.a.clock.J (j+1))
    (shelved:shelf' ≤ R.alloy.B.a.clock.J j) (slots:low.op.count ≤ Burn.horizon k+2)
    (halo:(eventually_atTop.mp (WilsonOriginalOccupiedRaffleIndependent.halo R simple)).choose ≤ j+1)
    (s:(marks).Mode)(x:Wallet A)(z:Wallet A')
    (h:ℕ)(tube:LinkTube G)(front:Hot (marks)→V)(mem:∀t,front t∈t.val.val)

    (placed:((vac).p.supportExponent+2)*((vac).p.B:ℝ)⁻¹ ≤ (σ)/2)
    {δ:ℝ}(dp:0 ≤ δ)(read:∀t:Hot (marks),t.val.val⊆s.val→
      Probe (both) (wages) (degrees) (WilsonOriginalCensusAngularFace.tests x z)
        (vac).p (fun _=>σ) (costs) (fun _=>WilsonEmittedCompactTariff.strip (σ)) (orders) (loads) (shelves) (gc)
        t (front t) ((home) (front t)) tube δ):
    WilsonOriginalMountedRegular.Filing R (vac) (highBook.row x) (lowerLaw z) s:=by
  let paid:=WilsonOriginalCensusRestamp.original R hk D Q π Γ Ψ course books (Nat.le_succ_of_le lo) cut ahead
    A K grades order shelf seats upperLaw high simple way pass month hospital fits narrow load q deep aged ep late
  have highArm:=paid.choose_spec.2.1
  have support:=paid.choose_spec.2.2.1
  have upper:Scene.Armada (stamped) (w₂) grades (σ) (budgetR R (j+1)) order high.op.count shelf:=
    { toMinistry:=highArm.toMinistry,positive:=highArm.positive,purchases:=highArm.purchases,honor:=highArm.honor
      suggests:=fun y=>budget_loosen (highArm.suggests y) paid.choose_spec.1 }
  have arms:(∀a:Bool,Scene.Armada ((both) a) ((wages) a) ((degrees) a) (σ) ((costs) a)
      ((orders) a) ((loads) a) ((shelves) a)):=by
    intro a
    cases a
    · exact upper
    · exact low.salary
  have aligned:Invoice.Supports (vac).p (fig).mist ((vac).p.supportExponent+2) (gc) (σ) (fig).limitC:=by
    convert support using 1
    ring
  have scope:(∀_:Bool,Invoice.Supports (vac).p (fig).mist ((vac).p.supportExponent+2) (gc) (σ)
      (WilsonEmittedCompactTariff.strip (σ))):=fun _=>WilsonEmittedCompactTariff.purchased aligned placed
  have receipt (t:Hot (marks))(ht:t.val.val⊆s.val):=WilsonOriginalCensusAngularFace.original
    (both) (wages) (degrees) (WilsonOriginalCensusAngularFace.tests x z) (vac).p (fun _=>σ) (costs)
    (fun _=>WilsonEmittedCompactTariff.strip (σ)) (orders) (loads) (shelves) (gc) t (front t) ((home) (front t)) tube
    arms scope (mem t) (read t ht)
  exact WilsonOriginalRestampedCensusFiling.original R simple hk D Q π Γ Ψ course books lo cut ahead
    A K A' K' grades grades' order shelf seats order' shelf' seats' upperLaw lowerLaw high low highBook lowBook
    way pass month hospital fits narrow load q deep aged ep late warm depth shelved slots halo s x z h tube front
    mem (fun t ht=>(receipt t ht).choose) dp (fun t ht=>(receipt t ht).choose_spec)

end YM.Integration.WilsonOriginalAdjacentAngularFiling
end
