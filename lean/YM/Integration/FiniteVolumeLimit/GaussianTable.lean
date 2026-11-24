import YM.Comparison.RG02.Bulk.Fk

/-!
Minimal local interface helper, not a claim of qlocal/FVA2 identification.

The following table is defined from RG02's independent action, sources and
Gaussian covariance. It is independent of the truncation order. The theorem
below only packages the already proved `Bulk.table` coefficient identity.
There is deliberately no theorem equating it with FVA2's `muLedger`/`solenoid`:
that is the remaining prescription-specific obligation. Only the source of
`Bulk.Fk` is imported; the large qlocal and FVA2 aggregate imports are omitted.
-/
set_option autoImplicit false
noncomputable section

namespace YM.FiniteVolumeGaussianTables
open Function Filter Finset MeasureTheory
open YM.RG YM.Lattice YM.Wilson YM.Precision YM.Exterior YM.Tree
open YM.Marker YM.Multi
open YM.Comparison.RG02 YM.Comparison.RG02.Order
open YM.Next.SectorChange
open scoped Classical BigOperators

variable {G : Gauge} {c f : Side} {S : StepData c f}
  {p : Clip} {P : PathData G} {O : ChartRatio G}
  {V : Type} [DecidableEq V] [Fintype V] {R : Census V}
  (K : Bulk.Kernel S p P O) (F : Forest S.ratio) (t : S.Choices)
  (W : Bulk.Colors R G f) (x : fieldDir G c 1)

def gaussianTable : PTable R := PowerSeries.mk fun n => Poly.inject fun i =>
  ∫ z, Assembly.rows
    (Assembly.expansions W.power (Bulk.markFn S F W) (Bulk.geometric K F t W))
    i n (Bulk.translated K F x z) ∂Gaussian.cloud (K.covariance F t)

theorem numerator_table (r : ℕ) :
    Bulk.Fk K F t W x r = Order.series R r (gaussianTable K F t W x) := by
  apply Order.Join.both_parts
  intro i a
  rw [Bulk.table, Order.polarization]
  simp only [gaussianTable, PowerSeries.coeff_mk, Poly.part, Poly.inject]

theorem normalized_table (r : ℕ) :
    Order.ratio (Bulk.Fk K F t W x r) =
      Order.ratio (Order.series R r (gaussianTable K F t W x)) := by
  rw [numerator_table]

theorem connected_table (r : ℕ) :
    Order.logMarked (Bulk.Fk K F t W x r) =
      Order.logMarked (Order.series R r (gaussianTable K F t W x)) := by
  rw [numerator_table]

end YM.FiniteVolumeGaussianTables

