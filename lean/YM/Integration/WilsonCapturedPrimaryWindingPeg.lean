import YM.Integration.WilsonCapturedPrimaryWindingMonomial

/-! Read the whole homogeneous thermal tensor from its time-one slice, including time-zero
directions and the scalar. The original rooted coordinate sum costs only the Taylor factorial. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryWindingPeg
open Function Filter Finset Tensor
open WilsonCapturedPrimaryWindingMonomial WilsonEmittedAngularJointFare
open scoped Classical BigOperators Topology ContDiff
variable {I : Type} [Fintype I]
local notation "pegBasis" => WilsonCapturedPrimaryWindingMonomial.basis

def tensor (b : (r:ℕ) → (Fin r → I) → ℂ) (d : ℕ) : Tensor.T (Space I) ℂ d :=
  ∑ r∈range (d+1), ∑ x, b r x • symmetrize (monomial (padded d x))

theorem symmetric (b : (r:ℕ) → (Fin r → I) → ℂ) (d : ℕ) : Sym (tensor b d) := by
  intro v p
  simp only [tensor,_root_.sum_apply,smul_apply]
  apply sum_congr rfl
  intro r _
  apply sum_congr rfl
  intro x _
  rw [symmetrize_sym _ v p]

theorem registered (b : (r:ℕ) → (Fin r → I) → ℂ) (d : ℕ) (y : I → ℝ) :
    diagonal (tensor b d) (1,y) = held b (fun v i=>(v i:ℂ)) d y := by
  simp only [tensor,diagonal,_root_.sum_apply,smul_apply,held,smul_eq_mul]
  apply sum_congr rfl
  intro r hr
  apply sum_congr rfl
  intro x _
  rw [← Tensor.diagonal, symmetrize_diagonal, slice (Nat.le_of_lt_succ (mem_range.mp hr))]

theorem cost [DecidableEq I] (b : (r:ℕ) → (Fin r → I) → ℂ) (d : ℕ) :
    ∑ u : Fin d → Option I, ‖tensor b d (pegBasis ∘ u)‖ ≤ mass b d := by
  let term := fun r (x:Fin r→I) (u:Fin d→Option I) =>
    ‖b r x‖ * ‖symmetrize (monomial (padded d x)) (pegBasis ∘ u)‖
  have budget (u : Fin d → Option I) : ‖tensor b d (pegBasis ∘ u)‖ ≤
      ∑ r∈range (d+1), ∑ x, term r x u := by
    simp only [tensor,_root_.sum_apply,smul_apply,term]
    apply (norm_sum_le ..).trans
    apply sum_le_sum
    intro r _
    simpa only [norm_smul] using norm_sum_le univ
      (fun x => b r x • symmetrize (monomial (padded d x)) (pegBasis ∘ u))
  apply (sum_le_sum fun u _=>budget u).trans
  rw [sum_comm]
  apply sum_le_sum
  intro r _
  rw [sum_comm]
  apply sum_le_sum
  intro x _
  dsimp only [term]
  rw [←mul_sum]
  exact (mul_le_mul_of_nonneg_left (symmetrized (padded d x)) (norm_nonneg _)).trans_eq (mul_one _)

theorem section_ext {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {d:ℕ} (T U:Tensor.T (ℝ×E) ℂ d) (st : Sym T) (su : Sym U)
    (on_slice:∀y:E, diagonal T (1,y)=diagonal U (1,y)) : T=U := by
  apply Tensor.ext_diag T U st su
  funext z
  obtain ⟨t,v⟩:=z
  have away (t:ℝ) (nz:t≠0) : diagonal T (t,v)=diagonal U (t,v) := by
    have scale : t • ((1:ℝ),t⁻¹ • v)=(t,v) := by simp [Prod.smul_mk,smul_smul,nz]
    rw [←scale,homogeneous,homogeneous,on_slice]
  by_cases nz:t≠0
  · exact away t nz
  · have ht : t=0 := not_ne_iff.mp nz
    subst t
    have at_zero (A:Tensor.T (ℝ×E) ℂ d) :
        Tendsto (fun u:ℝ=>diagonal A (u,v)) (𝓝[>] 0) (𝓝 (diagonal A (0,v))) :=
      ((A.cont.comp (continuous_pi fun _=>continuous_id.prodMk continuous_const)).tendsto 0).mono_left
        nhdsWithin_le_nhds
    have equal : (fun u:ℝ=>diagonal T (u,v)) =ᶠ[𝓝[>] 0] (fun u=>diagonal U (u,v)) := by
      filter_upwards [self_mem_nhdsWithin] with u hu using away u (ne_of_gt hu)
    exact tendsto_nhds_unique ((at_zero T).congr' equal) (at_zero U)

theorem germ [DecidableEq I] {d : ℕ} (F : Space I → ℂ) (smooth : ContDiffAt ℝ d F 0)
    (b : (r:ℕ) → (Fin r → I) → ℂ)
    (physical : ∀ y, diagonal (Tensor.coeff F d 0) (1,y)=held b (fun v i=>(v i:ℂ)) d y) :
    ∑ u : Fin d → Option I, ‖iteratedFDeriv ℝ d F 0 (pegBasis ∘ u)‖ ≤
      (d.factorial:ℝ)*mass b d := by
  have same := section_ext (Tensor.coeff F d 0) (tensor b d) (Tensor.coeff_symm smooth)
    (symmetric b d) (fun y=>(physical y).trans (registered b d y).symm)
  have restore : iteratedFDeriv ℝ d F 0=(d.factorial:ℝ) • tensor b d := by
    rw [←same]
    simp [Tensor.coeff,smul_smul,Nat.factorial_ne_zero]
  simp only [restore,smul_apply,norm_smul,Real.norm_natCast,←mul_sum]
  exact mul_le_mul_of_nonneg_left (cost b d) (Nat.cast_nonneg _)

end YM.Integration.WilsonCapturedPrimaryWindingPeg
