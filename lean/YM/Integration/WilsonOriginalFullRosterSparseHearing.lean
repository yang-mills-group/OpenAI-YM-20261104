import YM.Integration.WilsonOriginalFullRosterFiledHearing
import YM.Integration.WilsonOriginalSparseCensusEdge

/-! Finite sparse tests purchase the ordinary difference and its exact occupied credit on the
    authentic older Wilson receiver. The two posted children are aligned by the original calendar. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalFullRosterSparseHearing
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
variable (rows:∀i:ℕ,Config G (R.family.side i per) → Marker.Poly (Stock.census V))
variable (upper:WilsonOriginalDatedCensusInput.Filed (i:=j+1) (N:=N) R hk D Q π Γ Ψ books (Nat.le_succ_of_le base) ahead S a (rows (j+1+1)))
  (lower:WilsonOriginalDatedCensusInput.Filed (i:=j) (N:=N) R hk D Q π Γ Ψ books base ahead S' a' (rows (j+1)))
include rows simple in
/-- Consume the finite filed rank tests on every occupied subface against one fixed older group field. -/
theorem original {s:(marks).Mode}{charges:V→ℕ}{q h target:ℕ}{ε δ C:ℝ}
    (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)(live:j+1 < N)
    (way:WayStation R.kit)(pass:Pass D Q R.alloy R.kit)(month:Scholar.Month R.rolls D Q R.alloy.delay)
    (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (warm:Spill.Raffle.Warm G D R.alloy.delay φ)(nn:∀v,0 ≤ S v)(nn':∀v,0 ≤ S' v)
    (calendar:WilsonOriginalSparseCensusEdge.Calendar R simple hk D Q π Γ Ψ books base ahead
      (rows (j+1+1)) (rows (j+1)) upper lower charges q ε δ C)
    (seen:∀t:Hot (marks),t.val.val⊆s.val → WilsonOriginalSparseCensusEdge.Face R hk D Q π Γ Ψ books
      base ahead (rows (j+1+1)) (rows (j+1)) upper lower t (calendar.front t) charges calendar.tube target δ)
    (atStation:WilsonOriginalFullRosterDatedReturn.station R simple
      (WilsonOriginalFullRosterBookedHearing.roof upper.grades lower.grades charges target) (Fintype.card V) ≤ j)
    {df:ℕ}{frame:Frame G df}(section_:SectionData frame)(group:Hol G)(ticket:TicketP R.alloy R.kit D Q)
    (p:ℕ){tol:ℝ}(tp:0<tol)(mature:WilsonCenteredCaptureClock.first R simple ≤ j+1)
    (failure:(eventually_atTop.mp (WilsonOriginalFlatHaloRate.calendar R simple p tp)).choose ≤ j+1)
    {i:ℕ}(floor:m ≤ i)(older:i ≤ j+1)(fixed:WilsonSingleHardRadius.first R simple ≤ i)
    (U:Config G (R.family.side i per))(clear:flags (Ψ i).p.threshold U=∅):
    let read:=WilsonOriginalSparseCensusEdge.original (h:=h) R simple hk D Q π Γ Ψ books base ahead
      (rows (j+1+1)) (rows (j+1)) upper lower charges target course live way pass month hospital calendar nn nn' seen
    WilsonOriginalFullRosterFiledHearing.Earned R simple hk D Q π Γ Ψ books base ahead rows upper lower
      course live way pass month hospital read p tol older U:=by
  intro read
  exact WilsonOriginalFullRosterFiledHearing.original R simple hk D Q π Γ Ψ books base ahead rows
    upper lower course live way pass month hospital warm nn nn' read calendar.child atStation
    section_ group ticket p tp mature failure floor older fixed U clear

end YM.Integration.WilsonOriginalFullRosterSparseHearing
end
