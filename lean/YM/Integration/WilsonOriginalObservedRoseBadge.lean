import YM.Integration.WilsonOriginalObservedRoseJoint

/-! One independently dated signed invoice for each of the seven connected proper/full faces. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalObservedRoseBadge

open Filter Finset Function MeasureTheory Lattice Wilson Labels Source Extraction Table Spec
open Climb Trace.Pilot PhysMS PhysicalNext.Repeat.Legato Precision
open Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Structure1 XSpace.Rose XSpace.Cirrus XSpace.Photo
open WilsonSeparatedOriginalThermometerCells (positions)
open WilsonMaxwellThermometerShiftedPanel (cell)
open WilsonPositionThermometerCapStation (Group)
open WilsonOriginalObservedRoseJoint (fees locations lowerSite)
open WilsonOriginalObservedRoseCellPair (mass)
open WilsonOriginalObservedRoseFaces (linear fine)
open WilsonMaxwellThermometerPublicGalop (quotient)
open WilsonMaxwellThermometerFundedSecant (bill)
open WilsonThermometerPositionTunedGalop (loss originalRead)
open WilsonMaxwellThermometerSharedGroundFaces (tree)
open WilsonMaxwellThermometerSharedGroundPanel (change)
open scoped Classical BigOperators

variable {G : Gauge} (R : Run G) (D : ChartRatio G) (W : Initialize G) {V : Store G} (K : Pick V)
variable {f : Extraction.Order} {S : Table R.family.book} (F : Final R.family f S)
    (J : ℝ → tower S) (A : ℝ → Group R.family 6)
local notation "fit" => WilsonPositionCorrectedCap.adjusted F J V A

def receipt (r : ℝ) (z : ℕ×ℕ) (h : (fit r).station.k≤z.1) (m : Mesh)
    (p a : Tags G 6 3) (t : ℂ) (s : Finset (Fin 3)) : ℂ :=
  let c:=WilsonPositionThermometerGradedReading.row (fit r) z
  let x:=lowerSite R (fit r).station.k r z h
  let μ:=mass (Rose.test K) (positions (R:=R) r z) (cell m)
  ∑o:locations R z × m.Tuple (n:=3),
    let Q:=quotient W (V:=V) (x o.1) p
    let X:=originalRead R W (V:=V) (x o.1) p
    let L:=loss R W (V:=V) (x o.1) p
    let B:=fine W m o.2 a
    μ o*(bill (c o.1) (linear (Q 0) (Q 1) t) s *
      (c o.1 s-(X 0 s+t*X 1 s)+(L 0 s+t*L 1 s)) +
      bill (Q 0) B s*(tree R D W (V:=V) (x o.1) p s-change R W (V:=V) (x o.1) p s-B s))

theorem original (r : ℝ) (z : ℕ×ℕ) (h : (fit r).station.k≤z.1) (m : Mesh)
    (p a : Tags G 6 3) (t : ℂ) :
    (fees R D W K F J A r z h m p a t).1=
      ∑s:Finset (Fin 3),receipt R D W K F J A r z h m p a t s := by
  unfold receipt WilsonOriginalObservedRoseJoint.fees WilsonOriginalObservedRoseFaces.unpaid
  simp only [Finset.mul_sum]
  exact Finset.sum_comm

theorem empty (r : ℝ) (z : ℕ×ℕ) (h : (fit r).station.k≤z.1) (m : Mesh)
    (p a : Tags G 6 3) (t : ℂ) :
    receipt R D W K F J A r z h m p a t ∅=0 := by
  have none (c b:Finset (Fin 3)→ℂ) : bill c b ∅=0 := by
    unfold bill
    apply Finset.sum_eq_zero
    intro i _
    have occupied (j:Fin 7) : (∅:Finset (Fin 3)) ≠ WilsonMaxwellThermometerFundedSecant.faceKey j := by
      fin_cases j <;> decide
    exact if_neg (occupied i)
  simp [receipt,none]

end YM.Integration.WilsonOriginalObservedRoseBadge
