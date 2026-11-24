import YM.Integration.WilsonOriginalCoverNominalPair
import YM.Integration.WilsonPositionProgramNonbareDeposit

/-! At the same held field the first connected nominal is formed from three
one-mark declarations under one original vacuum, before the page division. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCoverNominalWords
open Function Filter Finset MeasureTheory RG Precision Lattice Wilson Exterior Tree
open Next.SectorChange PertExtension.Series Multi Marker Comparison.RG02
open Comparison.RG02.Cumulants Comparison.RG02.Laplace Comparison.RG02.Order
open WilsonPositionProgramPartitionedMaterial WilsonIndependentOrdinaryPairGrade
open scoped BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {p : Clip} {P : PathData G}
    {O : ChartRatio G} (K : Bulk.Kernel S p P O) (F : Forest S.ratio) (tag : S.Choices)
    {V : Type} [Fintype V] [DecidableEq V] {R : Census V} (C : Census Unit)
    (W : Bulk.Colors R G f) (A : fieldDir G c 1) (r : ℕ)

def ordinary (s : R.Mode) : Polynomial ℂ :=
  slot (C.fire ()) (render (Order.logMarked (Bulk.Fk K F tag (grouped W s C) A r)))

theorem each (hw : Bulk.Well W) (c₀ : ℝ) (D : BudgetPoint) (s : R.Mode) :
    slot s (render (Order.ratio (Bulk.Fk K F tag W A r))) = ordinary K F tag C W A r s := by
  ext j
  unfold ordinary
  simp only [coeff_slot,Order.render_coeff]
  by_cases hj : j≤r
  · exact WilsonPositionProgramNonbareDeposit.connected K F tag s C W hw A c₀ D r j hj
  · simp only [Order.observe,if_neg hj,Poly.part_nil]

theorem original (hw : Bulk.Well W) (c₀ : ℝ) (D : BudgetPoint)
    (a b : V) (s : R.Mode) (distinct : a≠b) (ab : s.val={a,b}) (j : ℕ) (hj : j≤r) :
    Laplace.detail (Order.logMarked (Bulk.Fk K F tag W A r)) s j =
      (ordinary K F tag C W A r s - ordinary K F tag C W A r (R.fire a) *
        ordinary K F tag C W A r (R.fire b)).coeff j := by
  rw [←each K F tag C W A r hw c₀ D s,←each K F tag C W A r hw c₀ D (R.fire a),
    ←each K F tag C W A r hw c₀ D (R.fire b)]
  exact WilsonOriginalCoverNominalPair.deposited _ (Bulk.fk_unit ..) (Bulk.fk_sym ..)
    a b s distinct ab j hj

end YM.Integration.WilsonOriginalCoverNominalWords
