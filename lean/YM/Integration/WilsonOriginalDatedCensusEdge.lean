import YM.Integration.WilsonOriginalCensusClockFiling
import YM.Integration.WilsonOriginalDatedCensusInput

/-! A signed angular reading of two independently appointed, adjacent physical posts.
The comparison is made against the lower post's declared unmasked group function. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalDatedCensusEdge
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
local notation "rank" => max ((∑v:V,upper.grades v)+1) ((∑v:V,lower.grades v)+1)

include incomingHigh incomingLow in
structure Reading (s:(marks).Mode)(charges:V → ℕ)(q h target:ℕ)(ε δ C:ℝ) where
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
  jets : ∀t:Hot (marks), t.val.val ⊆ s.val →
    WilsonOriginalCensusFiledProbe.Reading (roster (stamped) (low).model) (sides upper.grades lower.grades)
      (tests upper.x lower.x) (vac).p (fun _=>σ) (sides upper.order lower.order) (gc)
      t (front t) ((home) (front t)) tube (2*((fee charges t.val)+1)) target (2*((2:ℝ)^((fee charges t.val)+1))) δ
  upper_pole : (2:ℝ)^(upper.order+upper.shelf+1) ≤ C
  lower_pole : (2:ℝ)^(lower.order+lower.shelf+1) ≤ C
  high_rent : (8*(budgetR R (j+1))^(high).op.count)*(high).rent ≤ (regulatorRun R.family N per (j+1+1))^q

include simple incomingHigh incomingLow in
theorem original {s:(marks).Mode}{charges:V→ℕ}{q h target:ℕ}{ε δ C:ℝ}
    (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)(live:j+1 < N)
    (way:WayStation R.kit)(pass:Pass D Q R.alloy R.kit)(month:Scholar.Month R.rolls D Q R.alloy.delay)
    (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (warm:Spill.Raffle.Warm G D R.alloy.delay φ)(nn:∀v,0 ≤ S v)(nn':∀v,0 ≤ S' v)
    (read:Reading R simple hk D Q π Γ Ψ books base ahead incomingHigh incomingLow upper lower s charges q h target ε δ C)
    (budget:2 ≤ C)(small:regulatorRun R.family N per (j+1) ≤ 1)
    (cooled:(1+ε)*(regulatorRun R.family N per (j+1+1))^q ≤ 1):
    let γ:=regulatorRun R.family N per (j+1)
    let d:=fee charges s
    ∃F:WilsonOriginalMountedRegular.Filing R (vac) (upper.appointment.row upper.x) incomingLow s,
      F.α=(vac).p.supportExponent+1+1 ∧ F.W ≤ C*H^d ∧ F.gross ≤ C*H^2*(γ⁻¹)^(rank) ∧
      F.M ≤ C*H^(d+2)*(γ⁻¹)^(rank) ∧ F.rent ≤ (1+ε)*(regulatorRun R.family N per (j+1+1))^q ∧
      F.h=h ∧ F.δ=δ:=by
  intro γ d
  have upper_le (t:(marks).Mode):H^a*Poly.toll S t ≤ H^(nh)*Poly.toll S t:=
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (R.alloy.B.a.fits.delayed (j+1)).le read.high_degree)
      (Finset.prod_nonneg fun v _=>nn v)
  have lower_le (t:(marks).Mode):(R.alloy.B.a.clock.hatBeta j)^a'*Poly.toll S' t ≤
      (R.alloy.B.a.clock.hatBeta j)^(nl)*Poly.toll S' t:=
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (R.alloy.B.a.fits.delayed j).le read.low_degree)
      (Finset.prod_nonneg fun v _=>nn' v)
  obtain ⟨F,strip,wage,gross,complete,rent,crop,jet,_,_⟩:=
    WilsonOriginalCensusClockFiling.original R simple hk D Q π Γ Ψ course books base live ahead
      (actors) (nulls) (actors) (nulls) upper.grades lower.grades upper.order upper.shelf upper.seats
      lower.order lower.shelf lower.seats upper.law lower.law (high) (low) upper.appointment lower.appointment
      way pass month hospital read.fits read.narrow read.load q read.deep read.aged read.eps_pos read.late warm
      read.depth read.shelved read.slots read.halo s upper.x lower.x h read.tube read.front read.inside read.placed
      read.width S S' charges nn nn' upper_le lower_le read.high_wage read.low_wage read.income target read.delta_nn
      read.jets budget read.upper_pole read.lower_pole small read.high_rent cooled
  let outcome (returned:Config G (R.family.side (j+1) per) → Marker.Poly (Stock.census V)):Prop:=
    ∃F:WilsonOriginalMountedRegular.Filing R (vac) (upper.appointment.row upper.x) returned s,
      F.α=(vac).p.supportExponent+1+1 ∧ F.W ≤ C*H^d ∧ F.gross ≤ C*H^2*(γ⁻¹)^(rank) ∧
      F.M ≤ C*H^(d+2)*(γ⁻¹)^(rank) ∧ F.rent ≤ (1+ε)*(regulatorRun R.family N per (j+1+1))^q ∧
      F.h=h ∧ F.δ=δ
  have paid : outcome (lower.law lower.x):=⟨F,strip,wage,gross,complete,rent,crop,jet⟩
  exact (congrArg outcome lower.atInput).mp paid

end YM.Integration.WilsonOriginalDatedCensusEdge
end
