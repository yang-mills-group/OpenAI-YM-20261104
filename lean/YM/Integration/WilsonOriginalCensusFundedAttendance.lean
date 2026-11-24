import YM.Integration.WilsonOriginalCensusPhysicalAttendance
import YM.Integration.WilsonOriginalCensusPublicationClock

/-! A finite physical roster fixes its order, grades and seats first. Its joint
two-date weak-coupling and tuition thresholds then precede both regulators. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonOriginalCensusFundedAttendance
open Filter Finset Lattice Wilson RG Input Org PhysicalNext PhysicalNext.Repeat Legato
open QuadraticLocal QuadraticLocal.Mentor AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open WilsonOriginalCensusPhysicalAttendance WilsonOriginalCensusPublicationClock
open scoped BigOperators Classical

variable {G:Gauge}{n:ℕ}

structure Demand (q p:ℕ)(grades:Fin n → ℕ) where
  vac : ℕ
  order : ℕ
  shelf : ℕ
  school : Syl.School vac
  deep : 2 ≤ school.order
  fit : 1 ≤ Burn.horizon vac
  common : n ≤ Burn.horizon vac
  load : Load vac q order shelf p grades school.pieces (school.order+1)

def quote (q p:ℕ)(grades:Fin n → ℕ) : Demand q p grades :=by
  let order:=max q (2*(p+1)+8)
  let shelf:=∑v, grades v
  let vac:=n+order+shelf+p+4
  let pieces:=max 1 n
  have fit : 1 ≤ Burn.horizon vac := by simp only [Burn.horizon,vac]; omega
  have slots : pieces ≤ Burn.horizon vac+2 :=by simp only [pieces,Burn.horizon,vac];omega
  have whole : order+shelf ≤ Burn.horizon vac+2 :=by simp only [Burn.horizon,vac];omega
  let school:Syl.School vac:=⟨order,pieces,shelf,slots,by simp only [Burn.horizon,vac];omega,whole⟩
  refine ⟨vac,order,shelf,school,?_,fit,?_,?_⟩
  · change 2 ≤ max q (2*(p+1)+8)
    omega
  · simp only [Burn.horizon,vac];omega
  · change Load vac q order shelf p grades pieces (order+1)
    exact ⟨le_max_left ..,le_max_left ..,le_max_right ..,slots,le_rfl,le_rfl,whole,le_max_right ..,
      by simp only [vac];omega⟩

end YM.Integration.WilsonOriginalCensusFundedAttendance
end
