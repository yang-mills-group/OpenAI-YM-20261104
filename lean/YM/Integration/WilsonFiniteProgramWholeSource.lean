import YM.Comparison.RG02.Bare.Signals
import YM.Comparison.RG02.Laplace.Facing
import YM.Next.MULTISOURCE.Monomial

/-! A separately marked ordinary bare subword is the same insertion under the original
tagged kernel as its whole product with its total engineering degree. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonFiniteProgramWholeSource
open Function Filter Finset MeasureTheory RG Precision Lattice Wilson Exterior Tree
open Next.SectorChange PertExtension.Series Multi Marker Comparison.RG02
open Comparison.RG02.Cumulants Comparison.RG02.Laplace
open scoped Topology BigOperators Classical ContDiff

variable {G : Gauge} {c f : Side} {S : StepData c f} {p : Clip} {P : PathData G}
    {O : ChartRatio G} (K : Bulk.Kernel S p P O) (F : Forest S.ratio) (tag : S.Choices)
    {V J : Type} [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
    (R : Census V) (R' : Census J) (s : R.Mode) (j : J)
    (fields : V → ℝ → Config G f → ℂ) (degree : V → ℕ)

def whole (g : ℝ) (U : Config G f) := ∏ a∈s.val, fields a g U
def total := ∑ a∈s.val, degree a

private lemma ordinary (g c₀ : ℝ) (U : Config G f) :
    (Integral.model g c₀ (Bare.Signals.flare R fields degree) K U).part s =
      (Integral.weight g c₀ U (Bare.Signals.flare R fields degree) p P : ℝ) •
        ∏ a∈s.val, (g^degree a)⁻¹ • fields a g U := by
  unfold Integral.model
  rw [Poly.part_smul, Bare.Signals.singleton]
  change _ * (Poly.pass (∑ i, Poly.send (R.fire i) ((g^degree i)⁻¹ • fields i g U))).part s = _
  let coeff := fun i => (g^degree i)⁻¹ • fields i g U
  rw [show Poly.pass (∑ i, Poly.send (R.fire i) (coeff i)) =
      ∏ i, (1 + Poly.send (R.fire i) (coeff i)) from
    Multi.pass_sum_send Finset.univ (Multi.Hot.one R) coeff, Multi.polynomial]
  rfl

/-- The held configuration can be arbitrary and every source factor is evaluated on it. -/
theorem material (g c₀ : ℝ) (U : Config G f) :
    (Integral.model g c₀ (Bare.Signals.flare R fields degree) K U).part s =
      (Integral.model g c₀ (Bare.Signals.flare R' (fun _ => whole R s fields)
        (fun _ => total R s degree)) K U).part (R'.fire j) := by
  rw [ordinary, ordinary]
  change _ • _ = _ • ∏ a∈({j} : Finset J), (g ^ total R s degree)⁻¹ • whole R s fields g U
  rw [prod_singleton]
  congr 1
  simp only [whole, total, ← Finset.prod_pow_eq_pow_sum,
    Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_prod, Complex.ofReal_pow,
    Finset.prod_mul_distrib, Finset.prod_inv_distrib]

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
theorem normalized (W : Bulk.Colors R G f) (W' : Bulk.Colors R' G f) (b : R'.Mode)
    (A : fieldDir G c 1) (c₀ : ℝ) (D : BudgetPoint) (n : ℕ) (hw : Bulk.Well W)
    (hw' : Bulk.Well W')
    (vac : ∀ g U, (Integral.model g c₀ W K U).part R.quiet =
      (Integral.model g c₀ W' K U).part R'.quiet)
    (word : ∀ g U, (Integral.model g c₀ W K U).part s =
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
  have same : (fun g => (Order.unitScale (L g)).part s) =
      (fun g => (Order.unitScale (L' g)).part b) := by
    funext g
    simp only [Order.unitScale, Poly.part_smul]
    rw [portal_part K F tag W W' R.quiet R'.quiet A g c₀ B (vac g),
      portal_part K F tag W W' s b A g c₀ B (word g)]
  rw [same] at h₁
  exact Laplace.trial_gap h₁ h₂

/-- The Laplace coefficients agree on every tag, finite side and held direction. -/
theorem finite (A : fieldDir G c 1) (c₀ : ℝ) (D : BudgetPoint) (n : ℕ)
    (h : Bulk.Well (Bare.Signals.flare R fields degree))
    (hw : Bulk.Well (Bare.Signals.flare R' (fun _ => whole R s fields) (fun _ => total R s degree))) :
    ∀ k≤n, Laplace.detail (Bulk.Fk K F tag (Bare.Signals.flare R fields degree) A n) s k =
      Laplace.detail (Bulk.Fk K F tag (Bare.Signals.flare R' (fun _ => whole R s fields)
        (fun _ => total R s degree)) A n) (R'.fire j) k := by
  obtain ⟨U,hU,oU,hu⟩ := Laplace.one_look K F c₀ _ A D n h tag s
  obtain ⟨W,hW,oW,hw'⟩ := Laplace.one_look K F c₀ _ A D n hw tag (R'.fire j)
  let B := U ∩ W
  have hB : B ∈ 𝓝 1 := inter_mem hU hW
  have mB : MeasurableSet B := (oU.inter oW).measurableSet
  have h₁ := (hu B Set.inter_subset_left mB hB).2
  have h₂ := (hw' B Set.inter_subset_right mB hB).2
  have eqn := fun g : ℝ => portal_part K F tag _ _ s (R'.fire j) A g c₀ B
    (material K R R' s j fields degree g c₀)
  rw [funext eqn] at h₁
  exact Laplace.trial_gap h₁ h₂


end YM.Integration.WilsonFiniteProgramWholeSource

