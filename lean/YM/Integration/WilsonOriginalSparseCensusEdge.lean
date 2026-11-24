import YM.Integration.WilsonOriginalDatedCensusEdge
import YM.Integration.WilsonOriginalSparseFiledTotalPosted

/-! Sparse tests of the actual restamped and independently filed lower words on an original dated edge. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalSparseCensusEdge
open Function Finset Filter MeasureTheory Lattice Wilson RG Tree Marker QuadraticLocal Ac Source Labels
open QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Mentor QuadraticLocal.Affinity
open Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato AllOrder.Transit.WheelP
open AnalyticBridge VerifiedReset RemainderComparison Push Push.PriceCompiler Push.AbsoluteSums
open Stationary Comparison.RG02 QuadraticLocal.Rebirth VowsR LocalComparison ConnectedActivityE6
open OPE.Therm Multi WilsonRootedKioskOccupiedSlip WilsonOriginalSeparatedRegular
open WilsonOriginalSeparatedMask Comparison.Density.Transport Pert.Asymptotics
open WilsonOriginalCensusAngularFace
open scoped BigOperators Classical

variable {G:Gauge} (R:Run G) (simple:G.Simple) {m j N per k:ℕ}
  (hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)(Q:D.Tab R.rolls)
  (π:ℕ → Layout G)(Γ:ℕ → Pace.Coin)(Ψ:∀i,RG.Rep G (R.family.side i per))
  {φ:ℕ → ℕ}(books:Mentor.Offices.Books D R.rolls Q φ)(base:m ≤ j)
  (ahead:Mentor.Forecast D R.rolls Q φ books)
  {V:Type}[Fintype V][DecidableEq V]
local notation "marks" => Stock.census V
local notation "actors" => WilsonOriginalMixedBlockRows.room V
local notation "nulls" => fun _:V => (⊥:Submodule ℝ ℂ)
variable {S S': V → ℝ}{a a':ℕ}
variable (incomingHigh:Config G (R.family.side (j+1+1) per) → Marker.Poly (Stock.census V))
  (incomingLow:Config G (R.family.side (j+1) per) → Marker.Poly (Stock.census V))
variable (upper:WilsonOriginalDatedCensusInput.Filed (i:=j+1) (N:=N) R hk D Q π Γ Ψ books (Nat.le_succ_of_le base) ahead S a incomingHigh)
  (lower:WilsonOriginalDatedCensusInput.Filed (i:=j) (N:=N) R hk D Q π Γ Ψ books base ahead S' a' incomingLow)
local notation "high" => upper.post
local notation "low" => lower.post
local notation "vac" => Ψ (j+1)
local notation "student" => Oak.student (n:=per) R hk D Q π Γ books (Nat.le_succ_of_le base)
  (high).op (high).lesson ahead (actors) (high).model upper.order (high).voter
local notation "ζ" => Oak.grade0 R hk D Q π Γ (Nat.le_succ_of_le base) (high).lesson
local notation "stamped" => Mutation.stamp (student) (Γ (j+1)) (ζ) (Burn.horizon k+2) upper.order
local notation "home" => ((high).passport.coarser (R.family.path.levels.clock.op (j+1) per).ratio).origin
local notation "gc" => Coat.gStep (vac).beta
local notation "σ" => Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (j+1))
local notation "H" => R.alloy.B.a.clock.hatBeta (j+1)
local notation "nh" => ((∑v:V,upper.grades v)+1+5)*Fintype.card V
local notation "nl" => ((∑v:V,lower.grades v)+1+5)*Fintype.card V
local notation "fee" c:max t:max => WilsonOriginalCensusPostedWages.debit (max (nh) (nl)) c t

include incomingHigh incomingLow in
structure Calendar (charges:V → ℕ)(q:ℕ)(ε δ C:ℝ) where
  fits : upper.order ≤ Burn.horizon k+1
  narrow : upper.shelf ≤ R.alloy.B.a.clock.J (j+1)
  load : (high).op.count ≤ Burn.horizon k+2
  deep : 2*q+8 ≤ upper.order
  aged : q+3 ≤ 3*k+2
  eps_pos : 0 < ε
  late : WilsonReceivedMeasuredStampPrice.opening R simple q upper.order k deep aged eps_pos ≤ j+1
  depth : lower.order ≤ R.alloy.B.a.clock.J (j+1)
  shelved : lower.shelf ≤ R.alloy.B.a.clock.J j
  slots : (low).op.count ≤ Burn.horizon k+2
  halo : (eventually_atTop.mp (WilsonOriginalOccupiedRaffleIndependent.halo R simple)).choose ≤ j+1
  placed : ((vac).p.supportExponent+2)*((vac).p.B:ℝ)⁻¹ ≤ (σ)/2
  width : 0 < σ
  high_degree : a ≤ nh
  low_degree : a' ≤ nl
  high_wage : ∀v, S v ≤ H^(charges v)
  low_wage : ∀v, S' v ≤ H^(charges v)
  income : (eventually_atTop.mp (WilsonEmittedOriginalCalendar.wages R simple)).choose ≤ j+1
  tube : LinkTube G
  front : Hot (marks) → V
  inside : ∀t, front t ∈ t.val.val
  delta_nn : 0 ≤ δ
  upper_pole : (2:ℝ)^(upper.order+upper.shelf+1) ≤ C
  lower_pole : (2:ℝ)^(lower.order+lower.shelf+1) ≤ C
  high_rent : (8*(budgetR R (j+1))^(high).op.count)*(high).rent ≤ (regulatorRun R.family N per (j+1+1))^q
  child : ∀u,(low).passport.origin u=(home) u
  small : (gc) ≤ 1/2
  side : (vac).p.B=Nat.ceil ((Real.log H)^2)
  tax : (vac).p.supportExponent+2 ≤ 102
  reserve : Real.exp (((σ)⁻¹)^2) ≤ H

open Comparison.Density.Mirrors
open WilsonCapturedRootedAngularSlots WilsonCapturedPrimaryWindingMaterialRead WilsonNeutralTwoPrintPeg
open FVA1Physical FVA1Physical.TwoReset Further.PhysicalPeriodLimitF933 Macrame Shingle
open RegulatorIR RegulatorIR.Budget RegulatorIR.Diagram
open WilsonOriginalSparseFiledRanks (hull)
open WilsonOriginalSparseFiledOpening (near tail)
variable (t:YM.Multi.Hot (Stock.census V)) (v:V) (charges:V→ℕ) (tube:LinkTube G) (target:ℕ)
local notation "degrees" => sides upper.grades lower.grades
local notation "orders" => sides upper.order lower.order
local notation "S₀" => 2*((fee charges t.val)+1)
local notation "A₀" => 2*((2:ℝ)^((fee charges t.val)+1))
local notation "D₀" => WilsonOriginalCensusPhysicalLoad.rank (degrees)
local notation "pole₀" => WilsonOriginalCensusPhysicalLoad.head (degrees) t.val
local notation "height" => (pole₀)+WilsonOriginalCensusTariff.debit (S₀) (D₀)+target
local notation "lag" => WilsonOriginalCensusPhysicalLoad.delay (degrees) t.val
local notation "nodeSlots" => Site (R.family.side (j+1) per) × Loc G 1
local notation "hiPeek" T:max e:max y:max => (peek dvd_rfl (stamped) upper.grades (π (j+1)) T upper.x e y).part t.val
local notation "loPeek" T:max e:max y:max => (peek dvd_rfl (low).model lower.grades (π (j+1)) T lower.x e y).part t.val
local notation "outerBill" => (WilsonEmittedOutputPower.constant (height)+1)*
  (WilsonOriginalCensusFiledProbe.posted (A₀) (D₀))*(gc)^target

/-- The inputs at the actual sparse boards with the fixed tariff on this occupied face. -/
structure Face (δ:ℝ) where
  tape : Finset Age
  legal : Legal tape (π (j+1))
  power : ℕ
  readerPole : ℕ
  winding : ℝ
  positive : 0≤winding
  unit : ∀e,e+(pole₀)<3*(height) →
    ‖hiPeek tape e 0-loPeek tape e 0‖≤tail H power (pole₀) readerPole winding
  nodes : ∀e,e+(pole₀)<3*(height) → ∀r:ℕ,0<r → r≤e+(pole₀) → ∀Z:Fin r→nodeSlots,
    (∀u,Z u∈hull G ((home) v) ((vac).p.B/32)) → ∀F c,
    let y:=WilsonOriginalSparsePeg.probe (e+(pole₀)) Z F c
    ‖hiPeek tape e y-loPeek tape e y‖≤tail H power (pole₀) readerPole winding
  aperture : ℝ
  room : Room (vac).p (R.family.side (j+1) per) tube (vac).p.B aperture
  radius : 0≤aperture
  held : aperture≤2*(gc)^(1/2:ℝ)
  opened : WilsonOriginalSparseFiledOpening.starts G (height) (fee charges t.val)
    (near power (pole₀) readerPole)≤H
  reader : groupPrice tube 0≤H^readerPole
  begun : WilsonOriginalCensusTariffDate.Begun tube (Fintype.card V) (D₀) (3*(height)) (height) (orders) (lag) H
  precision : (H^power)⁻¹≤δ/3
  period : H^((pole₀)+readerPole+2)*winding≤δ/3
  remainder : (outerBill)≤δ/3

variable {q h:ℕ}{ε δ C:ℝ}
local notation "enroll" => Calendar R simple hk D Q π Γ Ψ books base ahead incomingHigh incomingLow upper lower charges q ε δ C
local notation "postedAt" seat:max => WilsonOriginalDatedCensusEdge.Reading R simple hk D Q π Γ Ψ books base ahead
  incomingHigh incomingLow upper lower seat charges q h target ε δ C
/-- Build each angular receipt from the two issued posts and the finite signed board reads. -/
def original {s:(marks).Mode} (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)(live:j+1<N)
    (way:WayStation R.kit)(pass:Pass D Q R.alloy R.kit)(month:Scholar.Month R.rolls D Q R.alloy.delay)
    (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (paid:enroll)(nn:∀u,0≤S u)(nn':∀u,0≤S' u)
    (seen:∀t:Hot (marks), t.val.val⊆s.val → Face R hk D Q π Γ Ψ books base ahead incomingHigh incomingLow
      upper lower t (paid.front t) charges paid.tube target δ):postedAt s:=by
  have upper_le (t:(marks).Mode):H^a*Poly.toll S t≤H^(nh)*Poly.toll S t:=
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (R.alloy.B.a.fits.delayed (j+1)).le paid.high_degree)
      (Finset.prod_nonneg fun u _=>nn u)
  have lower_le (t:(marks).Mode):(R.alloy.B.a.clock.hatBeta j)^a'*Poly.toll S' t≤
      (R.alloy.B.a.clock.hatBeta j)^(nl)*Poly.toll S' t:=
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (R.alloy.B.a.fits.delayed j).le paid.low_degree)
      (Finset.prod_nonneg fun u _=>nn' u)
  have receipts (t:Hot (marks))(sub:t.val.val⊆s.val):
      Nonempty (WilsonOriginalCensusFiledProbe.Reading (roster (stamped) (low).model) (sides upper.grades lower.grades)
        (tests upper.x lower.x) (vac).p (fun _=>σ) (sides upper.order lower.order) (gc)
        t (paid.front t) ((home) (paid.front t)) paid.tube (2*((fee charges t.val)+1)) target
        (2*((2:ℝ)^((fee charges t.val)+1))) δ):=by
    let f:=seen t sub
    obtain ⟨receipt⟩:=WilsonOriginalSparseFiledTotalPosted.original R simple hk D Q π Γ Ψ course books base live ahead
      (actors) (nulls) (actors) (nulls) upper.grades lower.grades upper.order upper.shelf upper.seats
      lower.order lower.shelf lower.seats upper.law lower.law (high) (low) upper.appointment lower.appointment
      f.tape upper.x lower.x t (paid.front t) charges paid.tube target f.power f.readerPole f.winding
      way pass month hospital paid.fits paid.narrow paid.load q paid.deep paid.aged paid.eps_pos paid.late
      paid.child (paid.inside t) S S' nn nn' upper_le lower_le paid.high_wage paid.low_wage paid.income
      f.legal f.positive f.unit f.nodes f.aperture f.room f.radius f.held paid.width paid.small paid.side
      paid.tax paid.reserve f.opened f.reader f.begun
    have cancel : δ/3+δ/3+δ/3 ≤ δ := by linarith
    exact ⟨⟨receipt.layout,receipt.tape,receipt.legal,receipt.ε,receipt.tolerance,receipt.entries,
      receipt.home,receipt.small,receipt.width,receipt.room,receipt.radius,receipt.held,receipt.hat,
      receipt.beta,receipt.thermal,receipt.atDate,receipt.side,receipt.tax,receipt.reserve,receipt.begun,
      receipt.quote.trans ((add_le_add (add_le_add f.precision f.period) f.remainder).trans cancel)⟩⟩
  refine ⟨paid.fits,paid.narrow,paid.load,paid.deep,paid.aged,paid.eps_pos,paid.late,paid.depth,paid.shelved,
    paid.slots,paid.halo,paid.placed,paid.width,paid.high_degree,paid.low_degree,paid.high_wage,paid.low_wage,
    paid.income,paid.tube,paid.front,paid.inside,paid.delta_nn,(fun t sub=>Classical.choice (receipts t sub)),paid.upper_pole,paid.lower_pole,paid.high_rent⟩

end YM.Integration.WilsonOriginalSparseCensusEdge
end
