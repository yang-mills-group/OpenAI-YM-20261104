import YM.Integration.WilsonOriginalObservedRoseBadge

/-! Independent dated ordinary rows are inserted on the original joint cell
before applying either signed secant. The price separates physical transport,
the finite thermal reading including its apparent-field shift, and the transfer
of the finite zero-order ground to the finer board. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalObservedRoseTransfer

open Filter Finset Function MeasureTheory Lattice Wilson Labels Source Extraction Table Spec
open Climb Trace.Pilot PhysMS PhysicalNext.Repeat.Legato Precision
open Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Structure1 XSpace.Rose XSpace.Cirrus XSpace.Photo
open WilsonSeparatedOriginalThermometerCells (positions)
open WilsonMaxwellThermometerShiftedPanel (cell)
open WilsonPositionThermometerCapStation (Group)
open WilsonOriginalObservedRoseJoint (fees locations lowerSite)
open WilsonOriginalObservedRoseCellPair (mass)
open WilsonOriginalObservedRoseFaces (Faces linear fine)
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

inductive Step
  | physical | thermal | ground

/-- The stage reads the independently filed ordinary table at its original
positions. The other argument of the joint cell is the auxiliary ground cell. -/
def amount (r:ℝ)(z:ℕ×ℕ)(h:(fit r).station.k≤z.1)(m:Mesh)
    (p a : Tags G 6 3) (t:ℂ)(s:Finset (Fin 3)) (filed:locations R z→Faces)(step:Step) : ℂ :=
  let c:=WilsonPositionThermometerGradedReading.row (fit r) z
  let x:=lowerSite R (fit r).station.k r z h
  let μ:=mass (Rose.test K) (positions (R:=R) r z) (cell m)
  ∑o:locations R z × m.Tuple (n:=3),
    let Q:=quotient W (V:=V) (x o.1) p
    let X:=originalRead R W (V:=V) (x o.1) p
    let L:=loss R W (V:=V) (x o.1) p
    let B:=fine W m o.2 a
    let cofactor:=bill (c o.1) (linear (Q 0) (Q 1) t) s
    μ o * match step with
      | .physical => cofactor*(c o.1 s-filed o.1 s)
      | .thermal => cofactor*(filed o.1 s-(X 0 s+t*X 1 s)+(L 0 s+t*L 1 s))
      | .ground => bill (Q 0) B s*(tree R D W (V:=V) (x o.1) p s-change R W (V:=V) (x o.1) p s-B s)

theorem original (r:ℝ)(z:ℕ×ℕ)(h:(fit r).station.k≤z.1)(m:Mesh)
    (p a : Tags G 6 3) (t:ℂ)(s:Finset (Fin 3)) (filed:locations R z→Faces) :
    let wage:=amount R D W K F J A r z h m p a t s filed
    WilsonOriginalObservedRoseBadge.receipt R D W K F J A r z h m p a t s =
      wage .physical+wage .thermal+wage .ground := by
  dsimp only
  unfold WilsonOriginalObservedRoseBadge.receipt amount
  rw [←Finset.sum_add_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro o _
  dsimp only
  ring

theorem purchased (r:ℝ)(z:ℕ×ℕ)(h:(fit r).station.k≤z.1)(m:Mesh)
    (p a : Tags G 6 3) (t:ℂ)(s:Finset (Fin 3)) (filed:locations R z→Faces)(price:Step→ℝ)
    (paid:∀step, ‖amount R D W K F J A r z h m p a t s filed step‖≤price step) :
    ‖WilsonOriginalObservedRoseBadge.receipt R D W K F J A r z h m p a t s‖≤
      price .physical+price .thermal+price .ground := by
  let wage:=amount R D W K F J A r z h m p a t s filed
  rw [original R D W K F J A r z h m p a t s filed]
  calc
    _ ≤ ‖wage .physical+wage .thermal‖+‖wage .ground‖ := norm_add_le _ _
    _ ≤ (‖wage .physical‖+‖wage .thermal‖)+‖wage .ground‖ := by gcongr; exact norm_add_le _ _
    _ ≤ _ := by gcongr <;> apply paid

end YM.Integration.WilsonOriginalObservedRoseTransfer
