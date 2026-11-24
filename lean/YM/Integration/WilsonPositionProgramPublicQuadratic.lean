import YM.Integration.WilsonPositionProgramPublicContrast
import YM.Extra.FREE_DETECTOR_ALGEBRA.WickPositive

/-! Uniform positivity in the actual finite coefficient norm and its
stability under signed errors in the entries of the reflected matrix. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionProgramPublicQuadratic
open Filter Function Set WilsonPositionProgramPublicContrast
open scoped Topology Classical BigOperators Matrix ComplexOrder
variable {I J : Type*} [Fintype I] [Fintype J]
theorem scaled (a:I→ℂ) (b:J→ℂ) (q:I→J→ℂ) (s t:ℂ) :
    assay (s•a) (t•b) q = (star s*t)*assay a b q := by
  simp only [assay,Pi.smul_apply,smul_eq_mul,star_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem subtracted (a:I→ℂ) (b:J→ℂ) (q p:I→J→ℂ) :
    assay a b (q-p) = assay a b q - assay a b p := by
  simp only [assay,Pi.sub_apply,mul_sub,Finset.sum_sub_distrib]

theorem charged (a:I→ℂ) : charge a≤Fintype.card I*‖a‖ := by
  calc
    _ ≤ ∑ _ : I, ‖a‖ := Finset.sum_le_sum fun i _=>norm_le_pi_norm a i
    _ = _ := by simp

private theorem unitVec {x:I→ℂ} (hx:x≠0) :
    ∃ y ∈ Metric.sphere (0:I→ℂ) 1, (‖x‖:ℂ)•y=x := by
  have hn := norm_pos_iff.mpr hx
  refine ⟨(‖x‖:ℂ)⁻¹•x,?_,?_⟩
  · rw [Metric.mem_sphere,dist_zero_right,norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hn.le,inv_mul_cancel₀ hn.ne']
  · rw [smul_smul,mul_inv_cancel₀ (by exact_mod_cast hn.ne'),one_smul]

theorem gap (q:I→I→ℂ) (positive:(Matrix.of q).PosDef) :
    ∃ k:ℝ, 0<k ∧ ∀x:I→ℂ, k*‖x‖^2≤‖assay x x q‖ := by
  have algebra (x:I→ℂ) : assay x x q = star x ⬝ᵥ (Matrix.of q *ᵥ x) := by
    simp only [assay,dotProduct,Matrix.mulVec,Matrix.of_apply,Pi.star_apply,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have co : Continuous (fun x:I→ℂ=>‖assay x x q‖) := by unfold assay; fun_prop
  by_cases pop : (Metric.sphere (0:I→ℂ) 1).Nonempty
  · obtain ⟨z,hz,least⟩ := (isCompact_sphere (0:I→ℂ) 1).exists_isMinOn pop co.continuousOn
    have nz : z≠0 := by rintro rfl; simp at hz
    have kp : 0<‖assay z z q‖ := norm_pos_iff.mpr (by rw [algebra]; exact (positive.dotProduct_mulVec_pos nz).ne')
    refine ⟨_,kp,fun x=>?_⟩
    by_cases null : x=0
    · simp [null,assay]
    obtain ⟨y,hy,eq⟩ := unitVec null
    have up := mul_le_mul_of_nonneg_right (least hy) (sq_nonneg ‖x‖)
    calc
      _ ≤ ‖assay y y q‖*‖x‖^2 := up
      _ = ‖assay ((‖x‖:ℂ)•y) ((‖x‖:ℂ)•y) q‖ := by
        simp only [scaled,norm_mul,norm_star,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
        ring
      _ = _ := by rw [eq]
  · refine ⟨1,one_pos,fun x=>?_⟩
    have eq : x=0 := by by_contra hn; obtain ⟨w,hw,_⟩ := unitVec hn; exact pop ⟨w,hw⟩
    simp [eq,assay]

theorem stable (q:I→I→ℂ) (positive:(Matrix.of q).PosDef) :
    ∃ k δ:ℝ, 0<k ∧ 0<δ ∧ ∀ (p:I→I→ℂ), ‖p-q‖≤δ →
      ∀x:I→ℂ, k*‖x‖^2 ≤ ‖assay x x p‖ := by
  obtain ⟨K,hK,original⟩ := gap q positive
  let n := (Fintype.card I:ℝ)
  let D := (1+n)^2
  have hn : 0≤n := Nat.cast_nonneg _
  have dp : 0<D := by dsimp [D]; positivity
  refine ⟨K/2,K/(2*D),half_pos hK,by positivity,?_⟩
  intro p paid x
  have hcharge : charge x ≤ (1+n)*‖x‖ := (charged x).trans <|
    mul_le_mul_of_nonneg_right (by dsimp [n]; linarith) (norm_nonneg _)
  have miss : ‖assay x x p-assay x x q‖ ≤ (K/2)*‖x‖^2 := by
    rw [← subtracted]
    calc
      _ ≤ charge x*charge x*‖p-q‖ := price .. 
      _ ≤ ((1+n)*‖x‖)*((1+n)*‖x‖)*(K/(2*D)) := by
        apply mul_le_mul _ paid (norm_nonneg _) (by positivity)
        exact mul_le_mul hcharge hcharge (Finset.sum_nonneg fun _ _=>norm_nonneg _) (by positivity)
      _ = _ := by dsimp [D]; field_simp
  have bound := norm_sub_norm_le (assay x x q) (assay x x p)
  rw [norm_sub_rev] at miss
  linarith [original x]

end YM.Integration.WilsonPositionProgramPublicQuadratic
