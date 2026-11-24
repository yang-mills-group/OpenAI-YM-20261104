import YM.Integration.WilsonReceivedChronologicalFixedEarner
import YM.Integration.WilsonOriginalOneArmOpticalDates
import YM.Integration.WilsonOriginalOneArmClearCash
import YM.Integration.WilsonOriginalSparseDatedHeat
import YM.Integration.WilsonOriginalPhysicalCorridorLength

/-! A finite roster's thermal and original occupied-gallery costs on one optical
collar. The opening precedes the physical cutoff, period, and held board. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalOneArmCurrentClock
open Filter Finset Lattice Wilson RG Marker MeasureTheory
open PhysicalNext PhysicalNext.Repeat Legato Org AllOrder AllOrder.Floe AllOrder.Floe.Step
open WilsonOriginalFullRosterCouplingClock
open WilsonRootedKioskOccupiedSlip WilsonCapturedPrimarySoftPartition
open scoped Classical BigOperators

variable {G:Gauge}(R:Run G)(simple:G.Simple){V:Type}[Fintype V][DecidableEq V]
open WilsonReceivedChronologicalFixedReserve (terms charges)
open WilsonReceivedChronologicalPanelClock (fare)
open WilsonReceivedChronologicalFixedEarner (programme start)

variable {n:ℕ}(grades power:Fin n→ℕ)(P cost:ℕ)(tol η:ℝ)(tp:0<tol)(ep:0<η)(np:0<n)
local notation "marks" => Stock.census (Fin n)
local notation "bill₀" => terms grades power P
local notation "A₀" => programme grades power P
local notation "C₀" => (2:ℝ)^((bill₀).order+(A₀).shelf+1)
local notation "debit₀" => (((∑v:Fin n,grades v)+1+5)*Fintype.card (Fin n))
local notation "rk₀" => (∑v:Fin n,grades v)+1

def each (s:(marks).Mode):ℕ:=
  let ask:=WilsonReceivedChronologicalFixedReserve.original grades power P R simple cost tol η tp ep
  (eventually_atTop.mp (WilsonOriginalOneArmOpticalDates.original R simple s n cost P
    (fare grades (charges power)) (rk₀) (2*s.val.card+((debit₀)+∑v∈s.val,2*(power v+4)))
    ((bill₀).precision+1) (C₀) η ask.choose np
    (fun t=>by simpa only [Fintype.card_fin] using t.val.card_le_univ) ep
    (Nat.add_le_add_right (bill₀).marked 1))).choose

def first:ℕ:=max (start grades power P R simple cost tol η tp ep)
  ((Finset.univ:Finset (marks).Mode).sup (each R simple grades power P cost tol η tp ep np))

theorem settled {j:ℕ}(early:first R simple grades power P cost tol η tp ep np≤j):
    start grades power P R simple cost tol η tp ep≤j ∧
    ∀s:(marks).Mode,each R simple grades power P cost tol η tp ep np s≤j+1:=by
  refine ⟨(le_max_left ..).trans early,fun s=>?_⟩
  exact (Finset.le_sup (f:=each R simple grades power P cost tol η tp ep np) (Finset.mem_univ s)).trans
    ((le_max_right ..).trans (early.trans (Nat.le_succ j)))

end YM.Integration.WilsonOriginalOneArmCurrentClock
end
