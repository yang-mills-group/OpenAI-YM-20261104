import YM.Integration.WilsonEmittedFiledMixedWindow

/-! An ordered thermal monomial has one nonzero coordinate in the physical time and link basis. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryWindingMonomial
open Function Finset Tensor
open scoped BigOperators Classical
variable {I : Type} [Fintype I] [DecidableEq I]
abbrev Space (I : Type) := ℝ × (I → ℝ)

def basis : Option I → Space I
  | none => (1,0)
  | some i => (0,fun j => if j=i then 1 else 0)

def coordinate : Option I → Space I →L[ℝ] ℂ
  | none => Complex.ofRealCLM.comp (ContinuousLinearMap.fst ..)
  | some i => Complex.ofRealCLM.comp
      ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ..))

omit [Fintype I] in
theorem dual (i j : Option I) : coordinate i (basis j) = if i=j then 1 else 0 := by
  cases i <;> cases j <;> simp [basis,coordinate,apply_ite]

def padded (d : ℕ) {r : ℕ} (x : Fin r → I) (i : Fin d) : Option I :=
  if h : i.val < r then some (x ⟨i.val,h⟩) else none

def monomial {d : ℕ} (s : Fin d → Option I) : Tensor.T (Space I) ℂ d :=
  (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin d) ℂ).compContinuousLinearMap
    (fun i => coordinate (s i))

theorem at_node {d : ℕ} (s u : Fin d → Option I) :
    monomial s (basis ∘ u) = if s=u then 1 else 0 := by
  simp only [monomial,ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebra_apply,Function.comp_apply,dual]
  by_cases e : s=u
  · subst u
    simp
  · rw [if_neg e]
    obtain ⟨i,hi⟩ : ∃i, s i≠u i := Classical.not_forall.mp (fun h => e (funext h))
    exact Finset.prod_eq_zero (mem_univ i) (if_neg hi)

omit [DecidableEq I] in
theorem slice {d r : ℕ} (hr : r≤d) (x : Fin r → I) (y : I → ℝ) :
    diagonal (monomial (padded d x)) (1,y) = ∏i,(y (x i):ℂ) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hr
  rw [diagonal,monomial,ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebra_apply,Fin.prod_univ_add]
  simp [padded,coordinate,Fin.castAdd,Fin.natAdd]

theorem permuted {d : ℕ} (s : Fin d → Option I) (p : Equiv.Perm (Fin d)) :
    ∑u : Fin d → Option I, ‖(monomial s).domDomCongr p (basis ∘ u)‖ = 1 := by
  have one (u : Fin d → Option I) :
      (monomial s).domDomCongr p (basis ∘ u) = if s ∘ p.symm=u then 1 else 0 := by
    change monomial s (basis ∘ (u ∘ p)) = _
    rw [at_node]
    congr 1
    apply propext
    constructor
    · intro h
      funext i
      simpa using congrFun h (p.symm i)
    · intro h
      funext i
      simpa using congrFun h (p i)
  simp [one,apply_ite]

theorem symmetrized {d : ℕ} (s : Fin d → Option I) :
    ∑u : Fin d → Option I, ‖(symmetrize (monomial s)) (basis ∘ u)‖ ≤ 1 := by
  let C : ℝ := Fintype.card (Equiv.Perm (Fin d))
  have pos : 0<C := Nat.cast_pos.mpr Fintype.card_pos
  have bound (u : Fin d → Option I) :
      ‖(symmetrize (monomial s)) (basis ∘ u)‖ ≤ C⁻¹*∑ p : Equiv.Perm (Fin d),
        ‖(monomial s).domDomCongr p (basis ∘ u)‖ := by
    simp only [symmetrize,smul_apply,_root_.sum_apply,norm_smul,Real.norm_eq_abs]
    change |C⁻¹| * _ ≤ _
    rw [abs_of_pos (inv_pos.mpr pos)]
    exact mul_le_mul_of_nonneg_left (norm_sum_le ..) (inv_nonneg.mpr pos.le)
  apply (sum_le_sum (fun u _ => bound u)).trans
  rw [← mul_sum,sum_comm]
  simp only [permuted,sum_const,card_univ,nsmul_eq_mul,mul_one]
  exact le_of_eq (inv_mul_cancel₀ pos.ne')

end YM.Integration.WilsonCapturedPrimaryWindingMonomial
