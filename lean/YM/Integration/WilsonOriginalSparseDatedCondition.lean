import YM.Integration.WilsonOriginalSparseCensusEdge
import YM.Integration.WilsonOriginalSparseDatedHeld
import YM.Integration.WilsonOriginalDatedCensusEdge
import YM.Integration.WilsonOriginalSparseFiledTotalPosted

/-! Sparse tests of the actual restamped and independently filed lower words on an original dated edge. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalSparseDatedCondition
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

/-- The signed numerical difference of the two actual dated prints. -/
def heard (tape:Finset Age)(power E:ℕ)(ω:ℝ)(e:ℕ)(Y:Stationary.Link G (R.family.side (j+1) per)):Prop:=
  ‖hiPeek tape e Y-loPeek tape e Y‖≤tail H power (pole₀) E ω

end YM.Integration.WilsonOriginalSparseDatedCondition
end
