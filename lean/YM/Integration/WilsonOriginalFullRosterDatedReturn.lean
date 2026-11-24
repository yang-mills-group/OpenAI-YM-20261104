import YM.Integration.WilsonOriginalFullRosterMountedPaid
import YM.Integration.WilsonOriginalFullRosterDatedOpening
import YM.Integration.WilsonOriginalFullRosterAngularPayment
import YM.Integration.WilsonOriginalCensusMountedPupils
import YM.Integration.WilsonOriginalPhysicalAngularFiling

/-! The shared-front return on the actual re-stamped original upper and the independently appointed lower. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalFullRosterDatedReturn
open Function Finset Filter MeasureTheory Lattice Wilson RG Tree Marker QuadraticLocal Ac Source Labels
open QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Mentor QuadraticLocal.Affinity
open Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato AllOrder.Transit.WheelP
open AnalyticBridge VerifiedReset RemainderComparison Push Push.PriceCompiler Push.AbsoluteSums
open Stationary Comparison.RG02 QuadraticLocal.Rebirth VowsR LocalComparison ConnectedActivityE6
open OPE.Therm Multi WilsonRootedKioskOccupiedSlip WilsonOriginalSeparatedRegular
open WilsonOriginalSeparatedMask Comparison.Density.Transport
open scoped BigOperators Classical
/-- A finite opening on the selected physical trajectory, chosen before any
cutoff, period, source board, test direction, and requested face. -/
def station {G:Gauge}(R:Run G)(simple:G.Simple)(T n:ℕ):ℕ:=
  (Filter.eventually_atTop.1 (WilsonOriginalFullRosterDatedOpening.original simple R T n)).choose

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
local notation "strip" => WilsonEmittedCompactTariff.strip (σ)
local notation "count" => fun _ : Bool => Fintype.card V
local notation "rank" => fun _ : Bool => WilsonOriginalCensusPhysicalLoad.rank (degrees)
open Comparison.Density Comparison.Density.Mirrors Comparison.RG02 Comparison.Density.Transport AnalyticBridge.SectorAffine.Offset
open WilsonOriginalFullRosterAngularReturn
include simple course cut in
theorem original (way:WayStation R.kit)(pass:Pass D Q R.alloy R.kit)(month:Scholar.Month R.rolls D Q R.alloy.delay)
    (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (fits:order ≤ Burn.horizon k+1)(narrow:shelf ≤ R.alloy.B.a.clock.J (j+1))
    (load:high.op.count ≤ Burn.horizon k+2)(q:ℕ)(deep:2*q+8 ≤ order)(aged:q+3 ≤ 3*k+2){ε:ℝ}(ep:0<ε)
    (late:WilsonReceivedMeasuredStampPrice.opening R simple q order k deep aged ep ≤ j+1)
    (child:∀v,low.passport.origin v=(home) v)
    (placed:((vac).p.supportExponent+2)*((vac).p.B:ℝ)⁻¹ ≤ (σ)/2)
    (s:(marks).Mode)(x:Wallet A)(z:Wallet A')(tube:LinkTube G)
    (front:Multi.Hot (marks)→V)(mem:∀t,front t∈t.val.val){δ:ℝ}
    (T:ℕ)(atStation:station R simple T (Fintype.card V) ≤ j)
    (measure:∀t:Multi.Hot (marks),t.val.val⊆s.val→
      Probe (both) (wages) (degrees) (tests x z) (vac).p (fun _=>σ) (costs) (fun _=>strip)
        (orders) (count) (rank) (gc) t (front t) ((home) (front t)) tube δ)
    (ranked:∀t (ht:t.val.val⊆s.val),(measure t ht).T ≤ T):
    (carried).hard=high.output.hard ∧
      (∀a,LocalComparison.actualPush R.family N per (j+1) (upperLaw a)=
        (Tint.Patrol.picture (stamped) (carried)).density a) ∧
      ∀(U:Config G (R.family.side (j+1) per)),
        (∀v∈s.val,Healthy (vac).p.threshold (neighborhood (vac).p.B ((home) v)) U)→
        ∀(t:Multi.Hot (marks)),t.val.val⊆s.val →
          ‖(WilsonRootedKioskOccupiedSlip.bare (L) x U).part t.val-
            (WilsonRootedKioskOccupiedSlip.bare (next) z U).part t.val‖ ≤
          δ:=by
  have root:=Nat.le_succ_of_le lo
  have live:=cut.le
  have gate {β H:ℝ}(bp:0<β)(coin:(gc)=(Real.sqrt β)⁻¹)(therm:β ≤ 2*H)
      (side:(vac).p.B=Nat.ceil ((Real.log H)^2)):
      64*(Fintype.card V+1) ≤ (vac).p.B ∧ ∀t r,t ≤ T → r ≤ Fintype.card V →
        WilsonOriginalFullRosterAngularPayment.opening t r ≤ Real.log H:=
    (Filter.eventually_atTop.1 (WilsonOriginalFullRosterDatedOpening.original simple R
      T (Fintype.card V))).choose_spec j atStation m N per k π Γ Ψ course root live bp coin therm side
  let H:=R.family.path.levels.clock.hatBeta (j+1)
  have point:=(course.1.walk (j+1) root live).truep.point
  have sides:(vac).p.B=Nat.ceil ((Real.log H)^2):=by rw [point];rfl
  have band:H/2 ≤ (vac).beta ∧ (vac).beta ≤ 2*H:=by
    rw [(course.1.walk (j+1) root live).beta]
    exact (R.makes.wilson.represents N per (j+1) live).band
  have hot:0<H:=zero_lt_one.trans (R.family.path.levels.fits.delayed (j+1))
  have positive:0<(vac).beta:=by linarith only [hot,band.1]
  have full:64*(Fintype.card V+1) ≤ (vac).p.B:=(gate positive rfl band.2 sides).1
  have subset:s.val.card ≤ Fintype.card V:=Finset.card_le_univ _
  have enrolled:64*(s.val.card+1) ≤ (vac).p.B:=(Nat.mul_le_mul_left 64 (Nat.succ_le_succ subset)).trans full
  apply WilsonOriginalFullRosterMountedPaid.original R simple hk D Q π Γ Ψ course
    books lo cut ahead A K A' K' grades grades' order shelf seats order' shelf' seats' upperLaw lowerLaw
    high low way pass month hospital fits narrow load q deep aged ep late child placed s x z tube front
    mem enrolled measure
  intro t ht
  let u:=measure t ht
  exact (gate u.beta_pos u.atDate u.thermal u.side).2 u.T s.val.card (ranked t ht) subset

end YM.Integration.WilsonOriginalFullRosterDatedReturn
end
