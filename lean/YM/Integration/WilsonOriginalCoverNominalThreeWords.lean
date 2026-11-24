import YM.Integration.WilsonOriginalCoverNominalWords
import YM.Integration.WilsonOriginalCoverNominalPartition

/-! All seven actual ordinary one-marker submissions in the next complete
connected nominal, on one held field and one conditional integral. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCoverNominalThreeWords
open Function Filter Finset MeasureTheory RG Precision Lattice Wilson Exterior Tree
open Next.SectorChange PertExtension.Series Multi Marker Comparison.RG02
open Comparison.RG02.Cumulants Comparison.RG02.Laplace Comparison.RG02.Order
open WilsonPositionProgramPartitionedMaterial WilsonIndependentOrdinaryPairGrade
open scoped BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {p : Clip} {P : PathData G}
    {O : ChartRatio G} (K : Bulk.Kernel S p P O) (F : Forest S.ratio) (tag : S.Choices)
    (C : Census Unit) (W : Bulk.Colors (WilsonSeparatedOriginalJointLog.three) G f)
    (A : fieldDir G c 1) (r : ℕ)
open WilsonSeparatedOriginalJointLog WilsonOriginalCoverNominalWords
local notation "J" => WilsonSeparatedOriginalJointLog.three
local notation "native" => Bulk.Fk K F tag W A r

theorem whole (hw : Bulk.Well W) (c₀ : ℝ) (D : BudgetPoint) (j : ℕ) (hj : j≤r) :
    Laplace.detail (Order.logMarked native) (shape univ) j =
      (WilsonOriginalCoverNominalCubic.cubic (fun a => ordinary K F tag C W A r (shape a))).coeff j := by
  have words : (fun a:Finset (Fin 3) => slot (shape a) (render (ratio native))) =
      (fun a => ordinary K F tag C W A r (shape a)) :=
    funext fun a => each K F tag C W A r hw c₀ D (shape a)
  rw [←words]
  exact WilsonOriginalCoverNominalCubic.deposited _ (Bulk.fk_unit ..) (Bulk.fk_sym ..) j hj

theorem entering (hw : Bulk.Well W) (c₀ : ℝ) (D : BudgetPoint) :
    let received := fun a:Finset (Fin 3) => slot (shape a)
      (logSeries (Fintype.card (Fin 3)+r) (render (ratio native)))
    let read := fun a:Finset (Fin 3) => ordinary K F tag C W A r (shape a)
    read univ =
      received univ + received {0,1} * read {2} + received {0,2} * read {1} +
        received {1,2} * read {0} + read {0} * read {1} * read {2} := by
  have words : (fun a:Finset (Fin 3) => slot (shape a) (render (ratio native))) =
      (fun a => ordinary K F tag C W A r (shape a)) :=
    funext fun a => each K F tag C W A r hw c₀ D (shape a)
  rw [←words]
  exact WilsonOriginalCoverNominalPartition.incoming _ (Bulk.fk_unit ..)

end YM.Integration.WilsonOriginalCoverNominalThreeWords
