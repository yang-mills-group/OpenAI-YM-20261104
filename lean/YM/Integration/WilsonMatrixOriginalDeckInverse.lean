import YM.Integration.WilsonMatrixOriginalDeckGram
import YM.Integration.WilsonMatrixTicketLanesNativePrices

/-! A localized compact test and a uniform inverse for the complete physical field basis. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalDeckInverse
open Matrix MeasureTheory Filter Set Pert Pert.Position MS MS.Land MS.Theater FVA2 FVA2.ColorCode
open Extraction Table Spec Climb MS.Local.Physical MS.Menus PhysicalNext.Repeat.Legato OPE.Levy RG11.Fields Pert.RawLabels Pert.Scale
open scoped Classical Topology BigOperators Matrix

private def vectorSize {I:Type*} [Fintype I] (z:I→ℂ) : ℝ := ∑i,‖z i‖
private def matrixSize {I:Type*} [Fintype I] (A:Matrix I I ℂ) : ℝ := ∑i,∑j,‖A i j‖

private theorem image_size {I:Type*} [Fintype I] (A:Matrix I I ℂ) (z:I→ℂ) :
    vectorSize (A *ᵥ z) ≤ matrixSize A * vectorSize z := by
  classical
  unfold vectorSize matrixSize
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j hj
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun b _ => norm_nonneg (z b)) hj) (norm_nonneg _)

private theorem cost_continuous {I:Type*} [Fintype I] : Continuous (@matrixSize I _) := by
  unfold matrixSize
  fun_prop

variable {G:Gauge} (R:Run G) (B:Deck G) {O:Booked B} {f:Extraction.Order} {S:Table R.family.book}
variable (F:Spec.Final R.family f S) (J:ℝ→PhysMS.tower S)

theorem purchased (leading:PhysMS.Leading F J) (M:MS_Data G O) (h:ℕ) {p:E4} (hp:(0:E4)≠p)
    (U:Set (Points 2)) (near:U∈𝓝 (Extra.FD.couple 0 p)) :
    ∃(g:Test 2) (C:ℝ), 0<C ∧ tsupport g⊆U ∧ (∀x, (g x).im=0 ∧ 0≤(g x).re) ∧
      0<(g (Extra.FD.couple 0 p)).re ∧ (∫x,g x)=1 ∧
      (∀μ:ℝ, IsUnit (MSSeparatedTestGram.matrix M h μ 0 g) ∧
        Tendsto (WilsonMatrixOriginalDeckGram.bank B F J h g) Trace.Pilot.trail
          (𝓝 (MSSeparatedTestGram.matrix M h μ 0 g)) ∧
        Tendsto (fun r=>(WilsonMatrixOriginalDeckGram.bank B F J h g r)⁻¹) Trace.Pilot.trail
          (𝓝 (MSSeparatedTestGram.matrix M h μ 0 g)⁻¹)) ∧
      ∀ᶠ r in Trace.Pilot.trail, IsUnit (WilsonMatrixOriginalDeckGram.bank B F J h g r) ∧
        ∀z:Glyph B h→ℂ, (∑i,‖z i‖) ≤ C*(∑i,‖(WilsonMatrixOriginalDeckGram.bank B F J h g r *ᵥ z) i‖) := by
  classical
  obtain ⟨g,support,real,atPoint,normalized,units⟩ :=
    MSSeparatedTestGram.simultaneous (WilsonMatrixTicketLanesNativePrices.warehouse R) M h hp U near
  let A := WilsonMatrixOriginalDeckGram.bank B F J h g
  let K := MSSeparatedTestGram.matrix M h 0 0 g
  let C := matrixSize K⁻¹+1
  have hC : 0<C := by dsimp [C,matrixSize]; positivity
  have stable := WilsonMatrixOriginalDeckGram.invertible B F J leading M h g 0 (units 0)
  have limit : Tendsto (fun r=>matrixSize (A r)⁻¹) Trace.Pilot.trail (𝓝 (matrixSize K⁻¹)) :=
    cost_continuous.continuousAt.tendsto.comp stable.2
  have bounded : ∀ᶠ r in Trace.Pilot.trail, matrixSize (A r)⁻¹<C :=
    (tendsto_order.mp limit).2 C (lt_add_one _)
  refine ⟨g,C,hC,support,real,atPoint,normalized,?_,?_⟩
  · intro μ
    exact ⟨units μ, WilsonMatrixOriginalDeckGram.original B F J leading M h g μ,
      (WilsonMatrixOriginalDeckGram.invertible B F J leading M h g μ (units μ)).2⟩
  · filter_upwards [stable.1,bounded] with r unit cap
    refine ⟨unit,fun z=>?_⟩
    change vectorSize z ≤ C*vectorSize (A r *ᵥ z)
    have same : (A r)⁻¹ *ᵥ (A r *ᵥ z) = z := by
      rw [mulVec_mulVec,nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp unit),one_mulVec]
    calc
      vectorSize z = vectorSize ((A r)⁻¹ *ᵥ (A r *ᵥ z)) := congrArg vectorSize same.symm
      _ ≤ matrixSize (A r)⁻¹ * vectorSize (A r *ᵥ z) := image_size _ _
      _ ≤ C*vectorSize (A r *ᵥ z) := mul_le_mul_of_nonneg_right cap.le (Finset.sum_nonneg fun _ _=>norm_nonneg _)

end YM.Integration.WilsonMatrixOriginalDeckInverse
