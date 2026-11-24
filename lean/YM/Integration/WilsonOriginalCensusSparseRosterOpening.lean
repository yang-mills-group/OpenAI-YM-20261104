import YM.Integration.WilsonOriginalCensusCanonicalSparseBudget
import YM.Integration.WilsonOriginalFullRosterBookedHearing

/-! The finite opening for the canonical sparse budget is chosen in the actual public grades before both regulators. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusSparseRosterOpening
open Function Finset Filter Lattice Wilson RG Tree Marker QuadraticLocal
open QuadraticLocal.Advent PhysicalNext.Repeat.Legato Comparison.Density.Transport
open WilsonOriginalCensusAngularFace (sides)
open WilsonOriginalSparseFiledOpening (near)
open scoped BigOperators Classical
variable {G:Gauge} (R:Run G)(simple:G.Simple)(tube:LinkTube G)
variable {V:Type}[Fintype V][DecidableEq V](d d':V→ℕ)(charges:V→ℕ)(hi lo target p:ℕ)
local notation "grades" => sides d d'
local notation "rank" => WilsonOriginalCensusPhysicalLoad.rank (grades)
local notation "work" => max (((∑v,d v)+1+5)*Fintype.card V) (((∑v,d' v)+1+5)*Fintype.card V)
local notation "bill" s:max => WilsonOriginalCensusPostedWages.debit (work) charges s
local notation "facePole" s:max => WilsonOriginalCensusPhysicalLoad.head (grades) s
local notation "height" s:max => (facePole s)+WilsonOriginalCensusTariff.debit (2*(bill s+1)) (rank)+target
local notation "C₀" s:max => (WilsonEmittedOutputPower.constant (height s)+1)*
  WilsonOriginalCensusFiledProbe.posted (2*((2:ℝ)^(bill s+1))) (rank)

def face (bought:2*(p+1)≤target)(s:(Stock.census V).Mode):ℕ:=
  (eventually_atTop.mp (WilsonOriginalCensusSparseFareCalendar.original R simple tube (Fintype.card V)
    (rank) (height s) (bill s) (facePole s) target p (sides hi lo) (WilsonOriginalCensusPhysicalLoad.delay (grades) s)
    (C₀ s) bought)).choose

def first (bought:2*(p+1)≤target):ℕ:=
  univ.sup (face R simple tube d d' charges hi lo target p bought)

theorem onset (bought:2*(p+1)≤target)(s:(Stock.census V).Mode):
    face R simple tube d d' charges hi lo target p bought s≤first R simple tube d d' charges hi lo target p bought:=
  Finset.le_sup (f:=face R simple tube d d' charges hi lo target p bought) (mem_univ s)

theorem ceiling (s:(Stock.census V).Mode):
    3*(height s)≤3*WilsonOriginalFullRosterBookedHearing.roof d d' charges target:=
  Nat.mul_le_mul_left 3 (Finset.le_sup (s:=univ) (f:=fun t=>(height t)) (mem_univ s))

end YM.Integration.WilsonOriginalCensusSparseRosterOpening
end
