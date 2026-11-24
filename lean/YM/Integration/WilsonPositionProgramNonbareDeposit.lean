import YM.Integration.WilsonPositionProgramNonbareFace
import YM.FVAAlt2.Lyric.Ground

/-! File the nonbare ordinary face as a connected singleton on its exact
older Wilson vacuum. Every coefficient is a function of the held direction. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPositionProgramNonbareDeposit
open Function Filter Finset MeasureTheory RG Precision Lattice Wilson Exterior Tree
open Next.SectorChange PertExtension.Series Multi Marker Comparison.RG02
open WilsonPositionProgramPartitionedMaterial
open FormalOPE.RG10 PowerSeries
open scoped Topology BigOperators Classical ContDiff

variable {G : Gauge} {c f : Side} {S : StepData c f} {p : Clip} {P : PathData G}
    {O : ChartRatio G} (K : Bulk.Kernel S p P O) (F : Forest S.ratio) (tag : S.Choices)
    {V : Type} [Fintype V] [DecidableEq V] {R : Census V} (s : R.Mode)
    (C : Census Unit) (W : Bulk.Colors R G f)
local notation "W'" => grouped W s C
local notation "Λ" => YM.FVAAlt2.Block.naked K F tag

omit [Fintype V] in
theorem vacuum (A : fieldDir G c 1) :
    (Λ).den (YM.FVAAlt2.Block.action K F tag A W) =
    (Λ).den (YM.FVAAlt2.Block.action K F tag A W') := rfl

theorem connected (hw : Bulk.Well W) (A : fieldDir G c 1) (c₀ : ℝ)
    (D : BudgetPoint) (n k : ℕ) (hk : k≤n) :
    Laplace.detail (Order.ratio (Bulk.Fk K F tag W A n)) s k =
    Laplace.detail (Order.logMarked (Bulk.Fk K F tag W' A n)) (C.fire ()) k := by
  have common := WilsonPositionProgramNonbareFace.original K F tag R s C W hw A c₀ D n k hk
  exact common.trans (Comparison.RG02.FVAAlt2.Lyric.logo (Bulk.fk_sym K F tag W' A n)
    (Bulk.fk_unit K F tag W' A n) () hk)

/-- Every normalized conditional numerator survives as the same power series
on the next date, with the unmarked term kept in the original denominator. -/
theorem deposited (hw : Bulk.Well W) (A : fieldDir G c 1) (D : BudgetPoint) :
    (Λ).step (YM.FVAAlt2.Block.action K F tag A W) (Word.read s (YM.FVAAlt2.Block.columns K F A W)) =
    (Λ).step (YM.FVAAlt2.Block.action K F tag A W') (Word.read (C.fire ()) (YM.FVAAlt2.Block.columns K F A W')) := by
  ext k : 1
  have h := WilsonPositionProgramNonbareFace.original K F tag R s C W hw A 0 D k k le_rfl
  change (Order.observe R k (Order.ratio (Bulk.Fk K F tag W A k)) k).part s =
    (Order.observe C k (Order.ratio (Bulk.Fk K F tag W' A k)) k).part (C.fire ()) at h
  rw [← YM.FVAAlt2.Block.positive_normalization K F tag A W k,
    ← YM.FVAAlt2.Block.positive_normalization K F tag A W' k,
    Order.observation R k _ le_rfl,Order.observation C k _ le_rfl,
    ← Word.unfold_see, ← Word.unfold_see, FlatFeed.close_part, FlatFeed.close_part] at h
  exact h

end YM.Integration.WilsonPositionProgramNonbareDeposit
