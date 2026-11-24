import YM.Integration.WilsonFiniteProgramWholeSource

/-! Signed finite sums of ordinary submitted words under one original forest and vacuum. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionProgramPortfolio
open Function Filter Finset MeasureTheory RG Precision Lattice Wilson Exterior Tree
open Next.SectorChange PertExtension.Series Multi Marker Comparison.RG02
open Comparison.RG02.Cumulants Comparison.RG02.Laplace
open scoped Topology BigOperators Classical ContDiff

variable {G : Gauge} {c f : Side} {S : StepData c f} {p : Clip} {P : PathData G} {O : ChartRatio G}
    (K : Bulk.Kernel S p P O) (F : Forest S.ratio) (tag : S.Choices)
    {V J I : Type} [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J] [Fintype I]
    {R : Census V} {R' : Census J} (W : Bulk.Colors R G f) (T : I → Bulk.Colors R' G f)
    (s : R.Mode) (b : R'.Mode) (a : I → ℂ) (A : fieldDir G c 1) (c₀ : ℝ)

private lemma portal_sum (B : Set (F.Slice G)) (hB : MeasurableSet B) (u : ℝ)
    (ht : ∀ i, Bulk.Well (T i))
    (words : ∀ U, (Integral.model u c₀ W K U).part s =
      ∑ i, a i * (Integral.model u c₀ (T i) K U).part b) :
    (Laplace.portal K F tag c₀ W A (fun _ => B) u).part s =
      ∑ i, a i * (Laplace.portal K F tag c₀ (T i) A (fun _ => B) u).part b := by
  let cut {Q : Type} [Fintype Q] [DecidableEq Q] {N : Census Q} (X : Bulk.Colors N G f) :=
    B.indicator (Actual.stack tag (Integral.sample u A) (Integral.temperature u)
      (Integral.model u c₀ X K) ∘ F.drape)
  have good (i : I) : Integrable (Actual.atMark b (cut (T i))) (F.order G) :=
    ((Actual.good_slice F tag (Integral.sample u A) (Integral.temperature u) K.branches
      (Integral.leaf_model K u c₀ (T i) (ht i))).on_window hB) b
  have reads (y : F.Slice G) :
      Actual.atMark s (cut W) y = ∑ i, a i * Actual.atMark b (cut (T i)) y := by
    by_cases hy : y ∈ B
    · simp only [cut,Actual.atMark,Set.indicator_of_mem hy,Function.comp_apply,Actual.stack,
        Poly.part_smul,words,mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    · simp [cut,Actual.atMark,Set.indicator_of_notMem hy]
  have measured : ∫ y, Actual.atMark s (cut W) y ∂F.order G =
      ∑ i, a i * ∫ y, Actual.atMark b (cut (T i)) y ∂F.order G := by
    simp_rw [reads]
    rw [integral_finsetSum _ (fun i _ => (good i).const_mul (a i))]
    simp_rw [integral_const_mul]
  change _ * (∫ y, Actual.atMark s (cut W) y ∂F.order G) =
    ∑ i, a i * (_ * (∫ y, Actual.atMark b (cut (T i)) y ∂F.order G))
  rw [measured,Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

private lemma vac_portal (X : Bulk.Colors R' G f) (B : Set (F.Slice G)) (u : ℝ)
    (h : ∀ U, (Integral.model u c₀ W K U).part R.quiet =
      (Integral.model u c₀ X K U).part R'.quiet) :
    (Laplace.portal K F tag c₀ W A (fun _ => B) u).part R.quiet =
      (Laplace.portal K F tag c₀ X A (fun _ => B) u).part R'.quiet := by
  simp only [Laplace.portal, Poly.part_smul, Actual.components]
  congr 1
  apply integral_congr_ae
  refine Eventually.of_forall fun y => ?_
  by_cases hy : y ∈ B
  · simp only [Actual.atMark, Set.indicator_of_mem hy, Function.comp_apply, Actual.stack,
      Poly.part_smul,h]
  · simp only [Actual.atMark, Set.indicator_of_notMem hy, Poly.part_nil]

private lemma sum_trial {n : ℕ} (x : I → ℕ → ℂ) (y : I → ℝ → ℂ) (h : ∀ j, Trial (x j) (y j) n) :
    Trial (fun k => ∑ j, a j * x j k) (fun u => ∑ j, a j * y j u) n := by
  have add (D : Finset I) : Trial (∑ j ∈ D, a j • x j) (∑ j ∈ D, a j • y j) n := by
    induction D using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      have zero : Tested.peval (0 : ℕ → ℂ) n = 0 := by
        funext u
        simp [Tested.peval,Zone.eval]
      unfold Trial
      rw [zero,sub_self]
      exact Laplace.bill_zero
    | @insert j D hj ih =>
      simpa only [Finset.sum_insert hj] using
        Laplace.trial_add (Laplace.trial_scale (a j) (h j)) ih
  convert add univ using 1 <;> funext z <;> simp [Finset.sum_apply]

/-- Normalized coefficients superpose on the actual common period even when the signed
finite portfolio uses a different source census. The zero mode keeps its whole held-field dependence. -/
theorem normalized (D : BudgetPoint) (n : ℕ) (hw : Bulk.Well W) (ht : ∀ i, Bulk.Well (T i))
    (vac : ∀ i u U, (Integral.model u c₀ W K U).part R.quiet =
      (Integral.model u c₀ (T i) K U).part R'.quiet)
    (words : ∀ u : ℝ, 0<u → ∀ U, (Integral.model u c₀ W K U).part s =
      ∑ i, a i * (Integral.model u c₀ (T i) K U).part b) :
    ∀ k≤n, Laplace.detail (Order.ratio (Bulk.Fk K F tag W A n)) s k =
      ∑ i, a i * Laplace.detail (Order.ratio (Bulk.Fk K F tag (T i) A n)) b k := by
  obtain ⟨U,hU,oU,hu⟩ := Laplace.find K F c₀ W A D n hw
  choose Q hQ oQ hq using fun i => Laplace.find K F c₀ (T i) A D n (ht i)
  let B := U ∩ ⋂ i, Q i
  have hB : B ∈ 𝓝 1 := inter_mem hU ((Filter.iInter_mem).mpr hQ)
  have mB : MeasurableSet B := (oU.inter (isOpen_iInter_of_finite oQ)).measurableSet
  let L := Laplace.portal K F tag c₀ W A (fun _ => B)
  let T' := fun i => Laplace.portal K F tag c₀ (T i) A (fun _ => B)
  have hL : Laplace.Fleet.Test (Bulk.Fk K F tag W A n) L :=
    fun q => (hu tag q B Set.inter_subset_left mB hB).2
  have hT (i : I) : Laplace.Fleet.Test (Bulk.Fk K F tag (T i) A n) (T' i) :=
    fun q => (hq i tag q B (Set.inter_subset_right.trans (Set.iInter_subset Q i)) mB hB).2
  have first := Laplace.Fleet.via (Bulk.fk_unit K F tag W A n) hL (Bulk.fk_sym K F tag W A n) s
  have last := sum_trial a _ _ (fun i => Laplace.Fleet.via (Bulk.fk_unit K F tag (T i) A n)
    (hT i) (Bulk.fk_sym K F tag (T i) A n) b)
  apply Laplace.trial_gap first
  refine Laplace.trial_congr ?_ last
  filter_upwards [show ∀ᶠ u : ℝ in Tested.germ, 0<u from self_mem_nhdsWithin] with u hu
  simp only [Order.unitScale,Poly.part_smul]
  rw [portal_sum K F tag W T s b a A c₀ B mB u ht (words u hu),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [vac_portal K F tag W A c₀ (T i) B u (vac i u)]
  ring

end YM.Integration.WilsonPositionProgramPortfolio
