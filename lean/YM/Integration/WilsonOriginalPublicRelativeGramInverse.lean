import YM.Integration.WilsonOriginalBlissMixedGram
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Ring.Units

/-! The measured square reference Gram determines the relative frame at a
second reporting date. Its own inverse pays both measured errors. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicRelativeGramInverse
open scoped Classical Matrix Matrix.Norms.Operator
variable {I:Type*}[Fintype I][DecidableEq I]
local notation "Mat"=>Matrix I I ℂ

theorem original (G C B Y S : Mat)(rank:IsUnit G.det)(u v:ℝ)
    (self:‖G-Bᴴ*S*B‖ ≤ u)(cross:‖C-Bᴴ*S*Y‖ ≤ v)(small:‖G⁻¹‖*u ≤ 1/2):
    IsUnit B.det ∧ ‖G⁻¹*C-B⁻¹*Y‖ ≤ 2*‖G⁻¹‖*(v+u*‖G⁻¹*C‖):=by
  let A:=Bᴴ*S*B
  let E:=Bᴴ*S*Y
  have inverse:=Matrix.nonsing_inv_mul G rank
  have close:‖1-G⁻¹*A‖<1:=by
    calc
      _ = ‖G⁻¹*(G-A)‖ := by rw [mul_sub,inverse]
      _ ≤ ‖G⁻¹‖*‖G-A‖ := norm_mul_le _ _
      _ ≤ ‖G⁻¹‖*u := mul_le_mul_of_nonneg_left self (norm_nonneg _)
      _ < 1 := lt_of_le_of_lt small (by norm_num)
  have aux:IsUnit (G⁻¹*A):=by simpa using (Units.oneSub (1-G⁻¹*A) close).isUnit
  have au:IsUnit A:=by
    have h:=((Matrix.isUnit_iff_isUnit_det G).mpr rank).mul aux
    rwa [←mul_assoc,Matrix.mul_nonsing_inv G rank,one_mul] at h
  have br:IsUnit B.det:=by
    have h:=(Matrix.isUnit_iff_isUnit_det A).mp au
    change IsUnit ((Bᴴ*S*B).det) at h
    rw [Matrix.det_mul] at h
    exact isUnit_iff_ne_zero.mpr (mul_ne_zero_iff.mp (isUnit_iff_ne_zero.mp h)).2
  refine ⟨br,?_⟩
  let H:=G⁻¹*C
  let X:=B⁻¹*Y
  have act:A*X=E:=by
    dsimp [A,E,X];rw [mul_assoc _ B,←mul_assoc B,Matrix.mul_nonsing_inv B br,one_mul]
  have change:H-X=G⁻¹*((C-E)-(G-A)*X):=by
    rw [sub_mul,act,show C-E-(G*X-E)=C-G*X by abel,mul_sub,←mul_assoc,inverse,one_mul]
  have u0:0 ≤ u:=(norm_nonneg _).trans self
  have uneven:‖X‖ ≤ ‖H‖+‖H-X‖:=by
    calc
      _ = ‖H-(H-X)‖ := by rw [sub_sub_cancel]
      _ ≤ _ := norm_sub_le _ _
  have paid:‖H-X‖ ≤ ‖G⁻¹‖*(v+u*‖H‖)+(‖G⁻¹‖*u)*‖H-X‖:=by
    calc
      _ = ‖G⁻¹*((C-E)-(G-A)*X)‖ := congr_arg norm change
      _ ≤ ‖G⁻¹‖*‖(C-E)-(G-A)*X‖ := norm_mul_le _ _
      _ ≤ ‖G⁻¹‖*(‖C-E‖+‖(G-A)*X‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _)
      _ ≤ ‖G⁻¹‖*(v+u*(‖H‖+‖H-X‖)) :=by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        exact add_le_add cross ((norm_mul_le _ _).trans (mul_le_mul self uneven (norm_nonneg _) u0))
      _ = _ := by ring
  have half:=mul_le_mul_of_nonneg_right small (norm_nonneg (H-X))
  change ‖H-X‖ ≤ 2*‖G⁻¹‖*(v+u*‖H‖)
  linarith only [half,paid]

end YM.Integration.WilsonOriginalPublicRelativeGramInverse
