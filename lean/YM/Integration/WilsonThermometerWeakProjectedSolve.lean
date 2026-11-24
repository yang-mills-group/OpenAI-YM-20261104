import YM.Integration.WilsonThermometerWeakPhysicalRank

/-! Recover the complete measured quotient coordinates after the genuine signed
two-point and relative Haar comparisons. The finite determinant includes the unit. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakProjectedSolve
open Function Set MeasureTheory Lattice RG Wilson Extraction Cells Next.Extract MergeProof Source
open Pert Pert.Position MS MS.Local.Physical MS.Menus MS.Land MS.Theater
open Matrix Push.RelayDifference FVA2 FVA2.ColorCode Extra.FD OPE.Levy RG11.Fields Pert.RawLabels Pert.Scale
open scoped Classical Topology BigOperators Matrix
variable {G:Gauge} (C:Family G)

theorem inverse_bound {I:Type*} [Fintype I] [DecidableEq I] (A:Matrix I I ℂ) (invertible:IsUnit A)
    (K:ℝ) (nonneg:0≤K) (priced:∀i j,‖A⁻¹ i j‖≤K) (t:I→ℂ):
    ‖t‖ ≤ ((Fintype.card I:ℝ)*K)*‖t ᵥ* A‖ := by
  have recovered:(t ᵥ* A) ᵥ* A⁻¹=t:=by rw [Matrix.vecMul_vecMul,Matrix.mul_nonsing_inv A (A.isUnit_iff_isUnit_det.mp invertible),Matrix.vecMul_one]
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro j
  calc
    ‖t j‖=‖((t ᵥ* A) ᵥ* A⁻¹) j‖:=by rw [recovered]
    _=‖∑i,(t ᵥ* A) i*(A⁻¹ i j)‖:=rfl
    _ ≤ ∑i,‖t ᵥ* A‖*K:= (norm_sum_le ..).trans (Finset.sum_le_sum (fun i _=>by
      rw [norm_mul];exact mul_le_mul (norm_le_pi_norm _ _) (priced i j) (norm_nonneg _) (norm_nonneg _)))
    _ = _ := by simp;ring

theorem original (B:Deck G) (d:ℕ) (V:∀d,Source.SectionData (C.labels.level d)) (W:Push.Mark.Weave G)
    {P:∀d,Cutoffs→(C.label d≃ₗ[ℂ]C.label d)} (a:Presentation C) {ζ:ℕ→ℕ→ℝ}
    (house:Hearthside C V W P a ζ) (i:Cutoffs)
    (E:(Glyph B d→ℂ) →ₗ[ℂ] C.label d)
    (L:C.label d →ₗ[ℂ] (Glyph B d→ℂ)) (A:Matrix (Glyph B d) (Glyph B d) ℂ)
    (detector:∀t,L (E t)=t ᵥ* A) (regular:IsUnit A) (I:ℝ) (hI:0≤I) (invoice:∀v w,‖A⁻¹ v w‖≤I)
    (x:C.label d) (τ H X Q:ℝ) (mixed:‖L x‖≤Q)
    (zero:∀t,a.step d i (E t)=0 → ‖L (E t)‖≤(τ*H)*‖t‖)
    (equation:∀t,a.step d i (E t)=a.step d i x → ‖L (E t)-L x‖≤τ*(X+H*‖t‖))
    (afford:2*((Fintype.card (Glyph B d):ℝ)*I)*(τ*H)≤1):
    ∃t:Glyph B d→ℂ,a.step d i (E t)=a.step d i x ∧
      ‖t‖≤2*((Fintype.card (Glyph B d):ℝ)*I)*(Q+τ*X):=by
  let K:ℝ:=(Fintype.card (Glyph B d):ℝ)*I
  have positive:0≤K:=by dsimp only [K];positivity
  have stable (t:Glyph B d→ℂ):‖t‖≤K*‖L (E t)‖:=by rw [detector];exact inverse_bound A regular I hI invoice t
  let F:=(a.step d i).toLinearMap.rangeRestrict.comp E
  have inj:Injective F:=by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro t ht
    have null:a.step d i (E t)=0:=congr_arg Subtype.val ht
    have small:‖t‖≤K*((τ*H)*‖t‖):=(stable t).trans (mul_le_mul_of_nonneg_left (zero t null) positive)
    have deficit:2*K*(τ*H)*‖t‖≤1*‖t‖:=mul_le_mul_of_nonneg_right afford (norm_nonneg t)
    exact norm_eq_zero.mp (by linarith only [norm_nonneg t,small,deficit])
  have dimensions:Module.finrank ℂ (Glyph B d→ℂ)=Module.finrank ℂ (LinearMap.range (a.step d i).toLinearMap):=by
    rw [Module.finrank_pi,WilsonThermometerWeakPhysicalRank.original C B d V W a house i]
  obtain ⟨t,box⟩:=(LinearMap.injective_iff_surjective_of_finrank_eq_finrank dimensions).1 inj
    ((a.step d i).toLinearMap.rangeRestrict x)
  have same:a.step d i (E t)=a.step d i x:=congr_arg Subtype.val box
  refine ⟨t,same,?_⟩
  have hearing:‖L (E t)‖≤Q+τ*(X+H*‖t‖):=by
    calc
      _ ≤ ‖L x‖+‖L (E t)-L x‖:=by
        have h:=norm_add_le (L x) (L (E t)-L x);rwa [add_sub_cancel] at h
      _ ≤ _:=add_le_add mixed (equation t same)
  have h:‖t‖≤K*(Q+τ*(X+H*‖t‖)):=(stable t).trans (mul_le_mul_of_nonneg_left hearing positive)
  have deficit:2*K*(τ*H)*‖t‖≤1*‖t‖:=mul_le_mul_of_nonneg_right afford (norm_nonneg t)
  change ‖t‖ ≤ 2*K*(Q+τ*X)
  linarith only [h,deficit]

end YM.Integration.WilsonThermometerWeakProjectedSolve
end
