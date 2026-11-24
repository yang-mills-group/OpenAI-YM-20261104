import YM.Integration.WilsonOriginalCensusSparseFareCalendar
import YM.Integration.WilsonMeasuredCourseQuietSlots

/-! A single period tolerance buys the actual sparse budgets on all masks of a paid finite family. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusCanonicalSparseBudget
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


/-- All occupied subsets use this same error at fixed report. -/
def winding (hat:ℝ)(p rank:ℕ):ℝ:=((hat^p)⁻¹/3)/(hat^(rank+1+1+2))

private theorem positive {hat:ℝ}(hh:0<hat)(p r:ℕ):0<winding hat p r:=by
  unfold winding
  positivity

private theorem sane {hat:ℝ}(hh:1≤hat)(p r k:ℕ)(short:k≤r+1):
    hat^(k+1+2)*winding hat p r ≤ (hat^p)⁻¹/3:=by
  have hp:0<hat:=zero_lt_one.trans_le hh
  have rooms:hat^(k+1+2)≤hat^(r+1+1+2):=pow_le_pow_right₀ hh (by omega)
  calc
    _ ≤ hat^(r+1+1+2)*winding hat p r:=mul_le_mul_of_nonneg_right rooms (positive hp p r).le
    _ = _:=by unfold winding;field_simp

local notation "C₀" => (WilsonEmittedOutputPower.constant (height)+1)*
  (WilsonOriginalCensusFiledProbe.posted (A₀) (D₀))
local notation "tape₀" => AllOrder.Floe.Step.tape (Burn.horizon k+2)

def opening (p:ℕ)(bought:2*(p+1)≤target):ℕ:=
  (eventually_atTop.mp (WilsonOriginalCensusSparseFareCalendar.original R simple tube (Fintype.card V)
    (D₀) (height) (fee charges t.val) (pole₀) target p (orders) (lag) (C₀) bought)).choose

/-- The numerical bill has been settled on the very same Wilson representative. Its period tolerance is
positive and depends on the common rank and date alone. -/
def original (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)(live:j+1≤N)
    (legal:Legal (tape₀) (π (j+1)))
    (p cap:ℕ)(ceiling:3*(height)≤cap)(bought:2*(p+1)≤target)
    (late:opening R simple hk D Q π Γ Ψ books base ahead incomingHigh incomingLow upper lower t charges tube target p bought≤j+1):
    WilsonOriginalSparseDatedFinance.Budget R hk D Q π Γ Ψ books base ahead incomingHigh incomingLow upper lower t charges tube
      target ((H^p)⁻¹) (p+1) 1 (winding H p (D₀)) cap:=by
  let selected:=WilsonMeasuredCourseQuietSlots.selected R π Γ Ψ course (Nat.le_succ_of_le base) live
  have params:(vac).p=R.family.path.levels.budget (j+1):=selected.1.symm.trans (R.makes.wilson.represents N per (j+1) live).vac
  have heat:(vac).beta=R.family.path.β N per (j+1):=(course.1.walk (j+1) (Nat.le_succ_of_le base) live).beta
  obtain ⟨site,nonnegative,thermal,gate,reader,begun,precision,rest⟩:=(eventually_atTop.mp
    (WilsonOriginalCensusSparseFareCalendar.original R simple tube (Fintype.card V) (D₀)
      (height) (fee charges t.val) (pole₀) target p (orders) (lag) (C₀) bought)).choose_spec (j+1) late
      N per live (vac) params heat
  have h1:1≤H:=(R.alloy.B.a.fits.delayed _).le
  exact ⟨ceiling,legal,(positive (zero_lt_one.trans_le h1) p (D₀)).le,_,site,nonnegative,thermal,gate,reader,
    begun,precision,sane h1 p (D₀) (pole₀) (WilsonOriginalCensusPhysicalLoad.cost (degrees) t.val),rest⟩

end YM.Integration.WilsonOriginalCensusCanonicalSparseBudget
end
