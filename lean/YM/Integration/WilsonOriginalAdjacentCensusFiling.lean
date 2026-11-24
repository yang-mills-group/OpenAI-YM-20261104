import YM.Integration.WilsonOriginalCensusMount
import YM.Integration.WilsonOriginalFreshJoinedRows
import YM.Integration.WilsonOriginalFreshPrintedGross

/-! Mount the three genuine programs from two adjacent original Wilson posts on a
single optical slice. The signed words read the unmasked output of the upper post
and the incoming independently submitted program of the next lower post. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalAdjacentCensusFiling
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
local notation "L" => rendered (student) (vac).p (Coat.gStep (Ψ ((j+1)+1)).beta)
local notation "next" => rendered low.model (vac).p (Coat.gStep (vac).beta)
local notation "home" => (high.passport.coarser (R.family.path.levels.clock.op (j+1) per).ratio).origin
private abbrev index {G:Gauge}{n:Side}{V T I:Type}[DecidableEq V]{J:Census V}{o:V→Site n}{b:BudgetPoint}
    (_:Lamps T I G b o J):Type:=I

include simple course cut in
def original (way:WayStation R.kit) (p:ℕ)(hardFloor:6*seats ≤ R.alloy.B.a.clock.J (j+1))
    (deep:2*(p+1)+8 ≤ order)(aged:p+4 ≤ 3*k+2)
    {ε:ℝ}(ep:0 < ε)(opened:WilsonFirstReceivedEarnedFee.opening R simple high.op.count p order k deep aged ep ≤ j+1)
    (warm:Spill.Raffle.Warm G D R.alloy.delay φ)(depth:order' ≤ R.alloy.B.a.clock.J (j+1))
    (shelved:shelf' ≤ R.alloy.B.a.clock.J j) (slots:low.op.count ≤ Burn.horizon k+2)
    (halo:(eventually_atTop.mp (WilsonOriginalOccupiedRaffleIndependent.halo R simple)).choose ≤ j+1)
    (row:WilsonOriginalOccupiedWindow.Slice R (marks) (vac)) (s:(marks).Mode) (x:Wallet A)(z:Wallet A')
    (arrived:row.A.E.log row.x=((L).join high.output.old).log x)
    (declared:∀U,lowerLaw z U=((vac).eval U:ℂ) • Poly.pass (WilsonRootedKioskOccupiedSlip.bare (next) z U))
    (h:ℕ)(tube:LinkTube G)(front:Hot (marks)→V)(mem:∀t,front t∈t.val.val)
    (words:∀t:Hot (marks),t.val.val⊆s.val→WilsonOriginalOrdinaryFlatHulls.Row (vac).p tube ((home) (front t))
      (fun U=>(WilsonRootedKioskOccupiedSlip.bare (L) x U).part t.val)
      (fun U=>(WilsonRootedKioskOccupiedSlip.bare (next) z U).part t.val))
    {δ:ℝ}(dp:0 ≤ δ)(due:∀t ht,(words t ht).price ≤ δ):
    WilsonOriginalMountedRegular.Filing R (vac) row (lowerLaw z) s:=by
  letI:Countable high.outputIndex:=high.outputCount
  letI:Countable high.modelIndex:=high.modelCount
  letI:Countable low.modelIndex:=low.modelCount
  letI:Countable (index (L)):=Scene.crewC high.model _ _ (Cruise.funded D R.rolls Q R.alloy φ books high.op
    (Oak.era R hk D Q π Γ (Nat.le_succ_of_le lo) high.op high.lesson)
    (R.alloy.B.a.S.oneStep (j+1) per).exact_size high.model order high.voter high.lesson.entry high.lesson.studied ahead)
  let d:=(∑v:V,grades v)+1
  have approved:∀a:(marks).Mode,(∑v∈a.val,grades v)+1 ≤ d:=fun _=>Nat.succ_le_succ
    (Finset.sum_le_sum_of_subset_of_nonneg (f:=grades) (subset_univ _) (fun _ _ _=>Nat.zero_le _))
  have upper:=WilsonOriginalFiledSuccessorIncome.original R hk D Q π Γ Ψ books (Nat.le_succ_of_le lo) cut
    ahead A K grades order shelf seats upperLaw high simple way course d p approved hardFloor deep aged ep opened
  have lower:=WilsonOriginalFreshPrintedGross.original R hk D Q π Γ Ψ course books lo (Nat.lt_of_succ_lt cut)
    ahead A' K' grades' order' shelf' seats' lowerLaw low simple warm depth shelved slots halo
  have hp:0 ≤ (vac).p.supportExponent+2:=by linarith only [(vac).p.exponent_pos]
  have np:0 ≤ (vac).p.supportExponent+1:=by linarith only [(vac).p.exponent_pos]
  exact WilsonOriginalCensusMount.join R (vac) row (lowerLaw z) s (L) high.output.old (next) x z
    (congrFun arrived) declared high.salary.positive low.salary.positive hp np upper.1 upper.2.2.1
    upper.2.1 lower.1 h tube front mem words dp due

end YM.Integration.WilsonOriginalAdjacentCensusFiling
end
