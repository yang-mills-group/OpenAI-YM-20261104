import YM.Integration.WilsonThermometerReferenceGrowth
import YM.Integration.WilsonPositionCorrectedCap
import YM.Integration.WilsonThermometerMarchNomination

/-! The actual grade-six field, both grade-four fields, and all omitted units on the one corrected star. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerMarchReference
open Function Filter Set Table Spec Extraction OPE OPE.Orbits Climb Trace Trace.Pilot Next.UVStress
open Lattice Wilson RG PhysicalNext.Repeat.Legato RG17 PhysMS PhysMS.Frame Maxwell XSpace XSpace.Normalize
open XSpace.Rose
open WilsonPositionThermometerCapStation WilsonPositionCapTransport WilsonPositionThermometerReading
open WilsonPositionThermometerGradedReading WilsonPositionThermometerGradedSource WilsonPositionCorrectedCap
open scoped Topology Classical BigOperators
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {T : Table R.family.book}
variable (F : Final R.family f T) (P : ℝ → tower T) (V : Store G) {H : (Bel R.family.book).Hierarchy}
    {l : Ultrafilter (ℕ × ℕ)} (A : ℝ → Group R.family 6)

def fee (C : Family G) (s : Badge) (i : Fin 3) : ℝ :=
  WilsonPositionThermometerStationNorm.cost C (grade i) * (‖source C s i‖ + costHint 0)

theorem original (simple : G.Simple) (paid : Book (f:=f) (l:=l) (H:=H) A P)
    (lead : Leading F P) (η : ℝ) (positive : 0<η) :
    ∀ᶠ r in trail, let Z:=adjusted F P V A r
      ∀ N p, Z.station.k<N → ∀ (s : Badge) (i : Fin 3),
        (R.family.labels.level (grade i)).coeffSize
          (Z.station.wheel.atCut (N,p) (index Z (grade i)) (vector Z s i)) ≤
          Real.exp (η * (-Real.log r)) * fee R.family s i := by
  let d : Badge × Fin 3 → Fin 7 := fun v=>grade v.2
  let v : ∀ j : Badge × Fin 3, (Bel R.family.book).Field (d j) := fun j=>source R.family j.1 j.2
  have book (m : ℕ) := WilsonPositionCorrectedCap.mixed F P V A paid lead d v m
  have go : Tendsto (fun r=>(adjusted F P V A r).station.k) trail atTop :=
    tendsto_atTop.mpr fun m=>(book m).mono fun _ h=>h.1
  have each (i : Fin 3) := WilsonThermometerReferenceGrowth.original (f:=f) (H:=H)
    simple R.makes (grade i) η positive
  filter_upwards [book 0,go.eventually (eventually_all.mpr each)] with r filed ready
  let Z:=adjusted F P V A r
  dsimp only
  intro N p upper s i
  have left := ready i Z.station (index Z (grade i)) rfl rfl filed.2.1 (vector Z s i) N p upper
  have radial : Z.station.wheel.r=r := filed.2.2.1
  rw [radial] at left
  have step : ‖vector Z s i-source R.family s i‖ ≤ costHint 0 := filed.2.2.2.2.2 (s,i)
  have bound : ‖vector Z s i‖ ≤ ‖source R.family s i‖ + costHint 0 := calc
    _ = ‖(vector Z s i-source R.family s i)+source R.family s i‖ := by rw [sub_add_cancel]
    _ ≤ ‖vector Z s i-source R.family s i‖ + ‖source R.family s i‖ := norm_add_le ..
    _ ≤ _ := by linarith only [step]
  exact left.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left bound (by unfold WilsonPositionThermometerStationNorm.cost; positivity))
    (Real.exp_pos _).le)

end YM.Integration.WilsonThermometerMarchReference
