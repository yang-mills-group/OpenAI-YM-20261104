import YM.Integration.WilsonPositionProgramPartitionedMaterial

/-! On a nonbare finite Wilson material, every ordinary face has an authentic
one-source realization under the same fixed forest and common older vacuum. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPositionProgramNonbareFace
open Function Filter Finset MeasureTheory RG Precision Lattice Wilson Exterior Tree
open Next.SectorChange PertExtension.Series Multi Marker Comparison.RG02
open Comparison.RG02.Cumulants Comparison.RG02.Laplace
open scoped Topology BigOperators Classical ContDiff

variable {G : Gauge} {c f : Side} {S : StepData c f} {p : Clip} {P : PathData G}
    {O : ChartRatio G} (K : Bulk.Kernel S p P O) (F : Forest S.ratio) (tag : S.Choices)
    {V J : Type} [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
    (R : Census V) (R' : Census J) (s : R.Mode) (j : J)


private lemma portal_part {R₁ : Census V} {R₂ : Census J} (W : Bulk.Colors R₁ G f)
    (W' : Bulk.Colors R₂ G f) (a : R₁.Mode) (b : R₂.Mode) (A : fieldDir G c 1)
    (g c₀ : ℝ) (B : Set (F.Slice G))
    (h : ∀ U, (Integral.model g c₀ W K U).part a = (Integral.model g c₀ W' K U).part b) :
    (Laplace.portal K F tag c₀ W A (fun _ => B) g).part a =
      (Laplace.portal K F tag c₀ W' A (fun _ => B) g).part b := by
  simp only [Laplace.portal, Poly.part_smul, Actual.components]
  congr 1
  apply integral_congr_ae
  refine Eventually.of_forall fun u => ?_
  by_cases hu : u ∈ B
  · simp only [Actual.atMark, Set.indicator_of_mem hu, Function.comp_apply, Actual.stack,
      Poly.part_smul, h]
  · simp only [Actual.atMark, Set.indicator_of_notMem hu, Poly.part_nil]

/-- The full vacuum divisor is common to a comparison of ordinary marked subwords,
even when the source census changes. -/
private theorem normalized (W : Bulk.Colors R G f) (W' : Bulk.Colors R' G f) (b : R'.Mode)
    (A : fieldDir G c 1) (c₀ : ℝ) (D : BudgetPoint) (n : ℕ) (hw : Bulk.Well W)
    (hw' : Bulk.Well W')
    (vac : ∀ g U, (Integral.model g c₀ W K U).part R.quiet =
      (Integral.model g c₀ W' K U).part R'.quiet)
    (word : ∀ g, 0<g → ∀ U, (Integral.model g c₀ W K U).part s =
      (Integral.model g c₀ W' K U).part b) :
    ∀ k≤n, Laplace.detail (Order.ratio (Bulk.Fk K F tag W A n)) s k =
      Laplace.detail (Order.ratio (Bulk.Fk K F tag W' A n)) b k := by
  obtain ⟨U,hU,oU,hu⟩ := Laplace.find K F c₀ W A D n hw
  obtain ⟨Q,hQ,oQ,hq⟩ := Laplace.find K F c₀ W' A D n hw'
  let B := U ∩ Q
  have hB : B ∈ 𝓝 1 := inter_mem hU hQ
  have mB : MeasurableSet B := (oU.inter oQ).measurableSet
  let L := Laplace.portal K F tag c₀ W A (fun _ => B)
  let L' := Laplace.portal K F tag c₀ W' A (fun _ => B)
  have hL : Laplace.Fleet.Test (Bulk.Fk K F tag W A n) L :=
    fun a => (hu tag a B Set.inter_subset_left mB hB).2
  have hL' : Laplace.Fleet.Test (Bulk.Fk K F tag W' A n) L' :=
    fun a => (hq tag a B Set.inter_subset_right mB hB).2
  have h₁ := Laplace.Fleet.via (Bulk.fk_unit K F tag W A n) hL (Bulk.fk_sym K F tag W A n) s
  have h₂ := Laplace.Fleet.via (Bulk.fk_unit K F tag W' A n) hL' (Bulk.fk_sym K F tag W' A n) b
  have same : (fun g => (Order.unitScale (L g)).part s) =ᶠ[Laplace.along]
      (fun g => (Order.unitScale (L' g)).part b) := by
    filter_upwards [self_mem_nhdsWithin (α:=ℝ) (a:=0) (s:=Set.Ioi 0)] with g hg
    simp only [Order.unitScale, Poly.part_smul]
    rw [portal_part K F tag W W' R.quiet R'.quiet A g c₀ B (vac g),
      portal_part K F tag W W' s b A g c₀ B (word g hg)]
  exact Laplace.trial_gap (Laplace.bill_congr (same.sub (EventuallyEq.rfl)) h₁) h₂


open WilsonPositionProgramPartitionedMaterial
open RegulatorIR.FVAAlt2.Booth

/-- Equality on the full Wilson group, ahead of the joint Gaussian and
any integration against the exterior. -/
theorem original (C : Census Unit) (W : Bulk.Colors R G f) (hw : Bulk.Well W)
    (A : fieldDir G c 1) (c₀ : ℝ) (D : BudgetPoint) (n : ℕ) :
    ∀ k≤n, Laplace.detail (Order.ratio (Bulk.Fk K F tag W A n)) s k =
      Laplace.detail (Order.ratio (Bulk.Fk K F tag (grouped W s C) A n)) (C.fire ()) k := by
  let W' := grouped W s C
  apply normalized K F tag R C s W W' (C.fire ()) A c₀ D n hw (admitted W s C hw)
  · intro g U
    simp only [Integral.model,Poly.part_smul,Integral.markedLog,
      Poly.pass_part _ (Multi.part_lit_quiet _)]
    rfl
  · intro g hg U
    simp only [Integral.model,Poly.part_smul]
    congr 1
    rw [Multi.first_pass () (Integral.markedLog g U W') (Multi.part_lit_quiet _)]
    rw [show (Integral.markedLog g U W').part (C.fire ())=
      (g^(W'.power (Arm.pub ())))⁻¹ • W'.mark (Arm.pub ()) g U from
      Multi.part_lit _ (Arm.pub ())]
    exact (rolled W s g hg.ne' U).symm

end YM.Integration.WilsonPositionProgramNonbareFace
