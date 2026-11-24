import YM.Integration.WilsonMacroscopicRichSignedMS

/-! The actual measured rich inverse minus the inverse of the independent
finite MS jet. Both inverse costs come from the same tree pivot. Their
remaining error is the signed two-field Wilson minus MS test itself. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichSignedInverse
open Function Matrix Pert Pert.Position MS MS.Local.Physical MS.Menus MS.Land MS.Theater
open FVA2 FVA2.ColorCode Extra.FD OPE.Levy RG11.Fields Pert.RawLabels Pert.Scale
open Extraction Table Spec Climb Filter Set Finset PhysMS MeasureTheory Next.UVStress
open scoped Classical Topology BigOperators
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book} (B : Deck G) {O : Booked B} (M : MS_Data G O)
variable (F : Spec.Final C f S) (J : ℝ→PhysMS.tower S)

def total {I : Type*} [Fintype I] (A : Matrix I I ℂ) : ℝ := ∑ i,∑ j,‖A i j‖

private theorem positive {I : Type*} [Fintype I] (A : Matrix I I ℂ) : 0≤total A := sum_nonneg fun _ _=>sum_nonneg fun _ _=>norm_nonneg _

private theorem point {I : Type*} [Fintype I] (A : Matrix I I ℂ) (i j : I) : ‖A i j‖≤total A :=
  (single_le_sum (fun j _=>norm_nonneg (A i j)) (mem_univ j)).trans (single_le_sum (fun i _=>sum_nonneg fun j _=>norm_nonneg (A i j)) (mem_univ i))

private theorem double {I : Type*} [Fintype I] (A D : Matrix I I ℂ) (i j : I) : ‖(A*D) i j‖≤total A*total D := by
  calc
    _ ≤ ∑ k,‖A i k*D k j‖ := norm_sum_le _ _
    _ ≤ ∑ k,‖A i k‖*total D := sum_le_sum fun k _=>by rw [norm_mul];exact mul_le_mul_of_nonneg_left (point D k j) (norm_nonneg _)
    _ = (∑ k,‖A i k‖)*total D := by rw [sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (single_le_sum (fun i _=>sum_nonneg fun k _=>norm_nonneg (A i k)) (mem_univ i)) (positive D)

private theorem triple {I : Type*} [Fintype I] (A D T : Matrix I I ℂ) (i j : I) : ‖(A*D*T) i j‖≤total A*total D*total T := by
  calc
    _ ≤ ∑ k,‖(A*D) i k*T k j‖ := norm_sum_le _ _
    _ ≤ ∑ k,(total A*total D)*‖T k j‖ := sum_le_sum fun k _=>by rw [norm_mul];exact mul_le_mul_of_nonneg_right (double A D i k) (norm_nonneg _)
    _ = (total A*total D)*(∑ k,‖T k j‖) := by rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_le_sum fun k _=>single_le_sum (fun l _=>norm_nonneg (T k l)) (mem_univ j)) (mul_nonneg (positive A) (positive D))

private theorem cont {I : Type*} [Fintype I] : Continuous (total (I:=I)) :=
  continuous_finsetSum _ fun i _=>continuous_finsetSum _ fun j _=>((continuous_apply j).comp (continuous_apply i)).norm

open WilsonMacroscopicRichSignedMS

theorem original (hG : G.Simple) (L : PhysMS.Leading F J) (h : ℕ) (g : Test 2) (μ : ℝ) (q : ℕ) {γ : ℝ→ℝ}
    (hγ : Trace.Pilot.Coupling G γ) (live : IsUnit (MSSeparatedTestGram.matrix M h μ 0 g)) :
    ∃ A : ℝ,0≤A ∧ ∀ᶠ r in Trace.Pilot.trail,
      let T := jet B M h g μ q (γ r)
      let W := WilsonMacroscopicRichMeasuredGram.bank B F J h g r
      let δ := defect B M F J h g μ q γ r
      IsUnit T ∧ IsUnit W ∧ T⁻¹-W⁻¹=W⁻¹*δ*T⁻¹ ∧ ∀ i j,‖(T⁻¹-W⁻¹) i j‖≤A*total δ := by
  let K := MSSeparatedTestGram.matrix M h μ 0 g
  let W := WilsonMacroscopicRichMeasuredGram.bank B F J h g
  let T := fun r=>jet B M h g μ q (γ r)
  have physical := WilsonMacroscopicRichMeasuredGram.invertible B F J L M h g μ live
  have ms := (WilsonMacroscopicRichSignedMS.continuous B M h g μ q).continuousAt.tendsto.comp (hγ.conforms hG)
  rw [at_zero] at ms
  have det : K.det≠0 := isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp live)
  have stable : ContinuousAt Inv.inv K := continuousAt_matrix_inv K (by rw [Ring.inverse_eq_inv'];exact continuousAt_inv₀ det)
  have seeT := stable.tendsto.comp ms
  have dets := ((continuous_id.matrix_det).continuousAt (x:=K)).tendsto.comp ms
  let fee := total K⁻¹+1
  have feePos : 0≤fee := by dsimp [fee];linarith only [positive K⁻¹]
  have thr : total K⁻¹<fee := lt_add_one _
  have bW := (cont.continuousAt.tendsto.comp physical.2).eventually (gt_mem_nhds thr)
  have bT := (cont.continuousAt.tendsto.comp seeT).eventually (gt_mem_nhds thr)
  refine ⟨fee*fee,mul_nonneg feePos feePos,?_⟩
  filter_upwards [RG17.positiveLength,physical.1,dets.eventually_ne det,bW,bT] with r rp wu td wp tp
  have tu : IsUnit (T r) := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr td)
  let δ := defect B M F J h g μ q γ r
  have name : δ=W r-T r := difference B M F J h g μ q γ rp
  have a : (W r)⁻¹*W r=1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp wu)
  have b : T r*(T r)⁻¹=1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp tu)
  have exactRow : (T r)⁻¹-(W r)⁻¹=(W r)⁻¹*δ*(T r)⁻¹ := by
    rw [name,mul_sub,sub_mul,a,one_mul,mul_assoc,b,mul_one]
  refine ⟨tu,wu,exactRow,fun i j=>?_⟩
  change ‖((T r)⁻¹-(W r)⁻¹) i j‖≤(fee*fee)*total δ
  rw [exactRow]
  calc
    _ ≤ total (W r)⁻¹*total δ*total (T r)⁻¹ := triple _ _ _ i j
    _ ≤ fee*total δ*fee := mul_le_mul (mul_le_mul_of_nonneg_right wp.le (positive δ)) tp.le (positive _) (mul_nonneg feePos (positive δ))
    _ = _ := by ring

end YM.Integration.WilsonMacroscopicRichSignedInverse
