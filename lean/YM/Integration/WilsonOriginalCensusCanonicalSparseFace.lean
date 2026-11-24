import YM.Integration.WilsonOriginalSparseDatedFinance

/-! Reduce each measured canonical two-print comparison to the exact nodes of the signed original receiver. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusCanonicalSparseFace
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
open WilsonOriginalSparseDatedFinance (Budget)
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

local notation "tape₀" => AllOrder.Floe.Step.tape (Burn.horizon k+2)

/-- The entire square-free occupied factor costs one on the actual incoming wallet. -/
private theorem weight {V:Type}[Fintype V][DecidableEq V](x:Wallet (WilsonOriginalMixedBlockRows.room V))(s:(Stock.census V).Mode):
    ‖∏v∈s.val,(x v).val‖≤1:=by
  exact (WilsonOriginalMixedBlockRows.project s x ()).property

/-- The two prints are tested on their common held link at all the actual thermal and angular grades. -/
def printed (δ:ℝ)(power E:ℕ)(wind:ℝ)(cap depth:ℕ)(kept:cap ≤ depth+1)
    (b:Budget R hk D Q π Γ Ψ books base ahead incomingHigh incomingLow upper lower t charges tube target δ power E wind cap)
    (cash:∀(e:ℕ),e ≤ depth → ∀Y:Stationary.Link G (R.family.side (j+1) per),‖Y‖ ≤ 1 →
      ‖hiPeek (tape₀) e Y-loPeek (tape₀) e Y‖ ≤ ‖∏w∈t.val.val,(upper.x w).val‖*wind):
    WilsonOriginalSparseCensusEdge.Face R hk D Q π Γ Ψ books base ahead incomingHigh incomingLow upper lower t v charges tube target δ:=by
  apply WilsonOriginalSparseDatedFinance.apply R hk D Q π Γ Ψ books base ahead incomingHigh incomingLow upper lower
    t v charges tube target δ power E wind cap b
  intro e active Y sampled
  have inside:e ≤ depth:=by omega
  have heard:=cash e inside Y sampled.bounded
  have unit:‖∏w∈t.val.val,(upper.x w).val‖*wind ≤ wind:=
    (mul_le_mul_of_nonneg_right (weight upper.x t.val) b.positive).trans_eq (one_mul wind)
  change _ ≤ ((H)^(near power (pole₀) E))⁻¹+wind
  exact (heard.trans unit).trans (le_add_of_nonneg_left (inv_nonneg.mpr
    (pow_nonneg (zero_le_one.trans (R.alloy.B.a.fits.delayed (j+1)).le) _)))

end YM.Integration.WilsonOriginalCensusCanonicalSparseFace
end
