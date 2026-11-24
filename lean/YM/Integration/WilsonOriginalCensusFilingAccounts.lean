import YM.Integration.WilsonOriginalAdjacentAngularFiling
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
namespace YM.Integration.WilsonOriginalCensusFilingAccounts
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
private abbrev index {G:Gauge}{n:Side}{V T I:Type}[DecidableEq V]{J:Census V}{o:V→Site n}{b:BudgetPoint}
    (_:Lamps T I G b o J):Type:=I


include simple course cut lowBook in
theorem original (way:WayStation R.kit)(pass:Pass D Q R.alloy R.kit)(month:Scholar.Month R.rolls D Q R.alloy.delay)
    (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (fits:order ≤ Burn.horizon k+1)(narrow:shelf ≤ R.alloy.B.a.clock.J (j+1))
    (load:high.op.count ≤ Burn.horizon k+2)(q:ℕ)(deep:2*q+8 ≤ order)(aged:q+3 ≤ 3*k+2){ε:ℝ}(ep:0<ε)
    (late:WilsonReceivedMeasuredStampPrice.opening R simple q order k deep aged ep ≤ j+1)
    (warm:Spill.Raffle.Warm G D R.alloy.delay φ)(depth:order' ≤ R.alloy.B.a.clock.J (j+1))
    (shelved:shelf' ≤ R.alloy.B.a.clock.J j) (slots:low.op.count ≤ Burn.horizon k+2)
    (halo:(eventually_atTop.mp (WilsonOriginalOccupiedRaffleIndependent.halo R simple)).choose ≤ j+1)
    (s:(marks).Mode)(x:Wallet A)(z:Wallet A')
    (h:ℕ)(tube:LinkTube G)(front:Hot (marks)→V)(mem:∀t,front t∈t.val.val)

    (words:∀t:Hot (marks),t.val.val⊆s.val→WilsonOriginalOrdinaryFlatHulls.Row (vac).p tube ((home) (front t))
      (fun U=>(WilsonRootedKioskOccupiedSlip.bare (L) x U).part t.val)
      (fun U=>(WilsonRootedKioskOccupiedSlip.bare (next) z U).part t.val))
    {δ:ℝ}(dp:0 ≤ δ)(due:∀t ht,(words t ht).price ≤ δ):

    let sale:=WilsonOriginalCensusRestamp.original R hk D Q π Γ Ψ course books (Nat.le_succ_of_le lo) cut ahead
      A K grades order shelf seats upperLaw high simple way pass month hospital fits narrow load q deep aged ep late
    let reg:=Invoice.price (vac).p (fig).mist (order+shelf+1) high.op.count ((vac).p.supportExponent+1+1)
      (fig).limitC G*sale.choose
    let χ:=R.alloy.B.a.clock.hatBeta (j+1)
    let other:=((2:ℝ)^(order'+shelf'+1)/(gc)^((∑v:V,grades' v)+1))*
      (Invoice.price (vac).p (MintClock.Page.temperature G 1 χ) (order'+shelf'+1) low.op.count
        ((vac).p.supportExponent+1) ((σ)/4) G*low.cost)
    ∃F:WilsonOriginalMountedRegular.Filing R (vac) (highBook.row x) (lowerLaw z) s,
    F.w=(w₂) ∧ F.w'=low.w ∧ F.α=(vac).p.supportExponent+1+1 ∧
    F.W=WilsonOriginalCensusMount.aperture (w₂) s ∧ F.W'=WilsonOriginalCensusMount.aperture low.w s ∧
    F.regular=reg ∧ F.rent=high.rent+ε*(Coat.gStep (R.family.path.rep N per ((j+1)+1)).beta)^q ∧
    F.gross=(2^(order+shelf+1)/(gc)^((∑v:V,grades v)+1))*reg ∧ F.nextGross=other ∧
    F.M=max (F.W*(F.regular+F.rent)) (F.W'*F.nextGross) ∧ F.h=h ∧ F.δ=δ ∧ sale.choose≤budgetR R (j+1):=by
  intro sale reg χ other
  letI:Countable high.outputIndex:=high.outputCount
  letI:Countable high.modelIndex:=high.modelCount
  letI:Countable low.modelIndex:=low.modelCount
  letI counted:Countable (index (Lu)):=Scene.crewC high.model _ _ (Cruise.funded D R.rolls Q R.alloy φ books high.op
    (Oak.era R hk D Q π Γ (Nat.le_succ_of_le lo) high.op high.lesson)
    (R.alloy.B.a.S.oneStep (j+1) per).exact_size high.model order high.voter high.lesson.entry high.lesson.studied ahead)
  letI:Countable (Mutation.Names (student) order):=@Mutation.instCountable _ _ _ _ _ _ _ _ (student) order counted
  obtain ⟨_,salary,_,paid,gross,old,_,_,_,eq,_⟩:=sale.choose_spec
  have nextSale:=WilsonOriginalFreshPrintedGross.original R hk D Q π Γ Ψ course books lo (Nat.lt_of_succ_lt cut)
    ahead A' K' grades' order' shelf' seats' lowerLaw low simple warm depth shelved slots halo
  have width:0 ≤ (vac).p.supportExponent+1+1:=by linarith only [(vac).p.exponent_pos]
  have width':0 ≤ (vac).p.supportExponent+1:=by linarith only [(vac).p.exponent_pos]
  let F:=WilsonOriginalCensusMount.join R (vac) (highBook.row x) (lowerLaw z) s (L) (carried).old (next) x z
    (congrFun ((highBook.mounted x).trans (eq x))) (lowBook.declared z) salary.positive low.salary.positive
    width width' paid old gross nextSale.1 h tube front mem words dp due
  exact ⟨F,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,sale.choose_spec.1⟩

end YM.Integration.WilsonOriginalCensusFilingAccounts
end
