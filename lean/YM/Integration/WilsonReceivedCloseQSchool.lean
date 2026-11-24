import YM.Integration.WilsonReceivedCloseQCalendar
import YM.Integration.WilsonReceivedCloseThreeSlotSchool
/-! Choose the genuine school room after the two fixed original source salaries and before the upper cutoff. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
universe u
namespace YM.Integration.WilsonReceivedCloseQSchool
open Pert.Asymptotics
open Function Filter Finset Lattice Wilson RG Tree Source Labels Marker QuadraticLocal Earn Sunrise QuadraticLocal.Affinity
open FVA1 Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard AllOrder AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Transit WheelP
open QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Rebirth AnalyticBridge VerifiedReset RemainderComparison
open ConnectedActivityE6 LocalComparison Mentor 
open WilsonPositionThermometerCapStation WilsonOriginalStarSceneWords WilsonOriginalThermometerPalette
open WilsonLimitConstruction WilsonOriginalStarSceneRent WilsonOriginalThermometerMicroscopic
open WilsonOriginalThermometerTopDensity
open scoped Classical BigOperators


variable (d mark rank shelf q:ℕ)
def precision := 2*d*mark+(q+(2*d+1)*mark+1+mark)+3
def degree := max rank (2*(precision d mark q+1)+8)
def vacuum := degree d mark rank q+shelf+mark
def school : Syl.School (vacuum d mark rank shelf q) :=
  ⟨degree d mark rank q,mark,shelf,by unfold vacuum Burn.horizon; omega,
    by unfold vacuum Burn.horizon; omega, by unfold vacuum Burn.horizon; omega⟩
theorem resources :
    2*(precision d mark q+1)+8 ≤ (school d mark rank shelf q).order ∧
    precision d mark q+4 ≤ 3*vacuum d mark rank shelf q+2 ∧
    rank ≤ (school d mark rank shelf q).order := by
  have deep : 2*(precision d mark q+1)+8≤degree d mark rank q := le_max_right .. 
  exact ⟨deep, by unfold vacuum; omega, le_max_left ..⟩
end YM.Integration.WilsonReceivedCloseQSchool
