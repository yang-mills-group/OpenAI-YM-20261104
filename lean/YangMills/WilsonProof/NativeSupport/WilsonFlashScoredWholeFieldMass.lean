import YangMills.WilsonProof.NativeSupport.SeparatedCorrelationBounds

noncomputable section
namespace YM.Integration.WilsonFlashScoredWholeFieldMass
open YangMills YangMills.Matching
open scoped BigOperators Classical

variable {g : GaugeGroup} {B : Maxwell.Reference g} {h : ℕ}

private theorem partialMass (y : B.sector h) (S : Finset (B.toCoordinates.Key →₀ ℕ)) :
    ∑ m ∈ S, ‖MvPolynomial.coeff m y.val‖ ≤ sectorMass y := by
  classical
  calc
    _ = ∑ m ∈ S ∩ y.val.support, ‖MvPolynomial.coeff m y.val‖ := by
      symm
      apply Finset.sum_subset Finset.inter_subset_left
      intro m hm excluded
      have absent : m ∉ y.val.support := fun present => excluded (Finset.mem_inter.mpr ⟨hm, present⟩)
      rw [MvPolynomial.notMem_support_iff.mp absent, norm_zero]
    _ ≤ sectorMass y :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right (fun m _ _ => norm_nonneg _)

/-- For each output field a contractive public linear reading attains its full coefficient mass. -/
theorem attained (x : B.sector h) :
    ∃ out : B.sector h →ₗ[ℂ] ℂ, (∀ y, ‖out y‖ ≤ sectorMass y) ∧ ‖out x‖ = sectorMass x := by
  classical
  let phase (z : ℂ) : ℂ := (‖z‖ : ℂ) / z
  have bounded (z : ℂ) : ‖phase z‖ ≤ 1 := by
    by_cases hz : z = 0
    · simp [phase, hz]
    · simp [phase, norm_ne_zero_iff.mpr hz]
  have cancel (z : ℂ) : phase z * z = (‖z‖ : ℂ) := by
    by_cases hz : z = 0
    · simp [phase, hz]
    · exact div_mul_cancel₀ _ hz
  let out : B.sector h →ₗ[ℂ] ℂ := ∑ m ∈ x.val.support,
    phase (MvPolynomial.coeff m x.val) • ((MvPolynomial.lcoeff ℂ m).comp (B.sector h).subtype)
  have read (y : B.sector h) :
      out y = ∑ m ∈ x.val.support, phase (MvPolynomial.coeff m x.val) * MvPolynomial.coeff m y.val := by
    simp only [out, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
      Submodule.subtype_apply, MvPolynomial.lcoeff_apply, smul_eq_mul]
  refine ⟨out, fun y => ?_, ?_⟩
  · rw [read]
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun m _ => ?_)).trans (partialMass y x.val.support))
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (bounded _)
  · rw [read]
    simp_rw [cancel]
    rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (sectorMass_nonneg x)

end YM.Integration.WilsonFlashScoredWholeFieldMass
end
