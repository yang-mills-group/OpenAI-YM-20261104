import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic -- exists olean?

/-!
# Flag and scale transport arithmetic

Index by *physical* grade (pieces of a stipulated compatible filtration), not by the number
of slots used to present a field. The argument here only assumes a finite grading, so applies
also before an identification of particular physical bases (and to quotients, e.g. swap V for
just the blocks through degree h). Later we connect it to fields.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Frames
open Function Finset Filter
open scoped Topology BigOperators

variable {d : ℕ}
abbrev Grade (d : ℕ) := Fin (d+1)
abbrev Col (V : Grade d → Type) := ∀ i, V i
variable (V : Grade d → Type) [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace ℂ (V i)]

abbrev put (i : Grade d) (x : V i) : Col V := Pi.single i x

abbrev BlockMatrix := Module.End ℂ (Col V)

abbrev block (A : BlockMatrix V) (i j : Grade d) (x : V j) := A (put V j x) i

/-- These matrices can't take us through any grade from low to high. -/
def triangular (A : BlockMatrix V) := ∀ i j : Grade d, j < i → ∀ x, block V A i j x = 0

omit [∀ i, NormedSpace ℂ (V i)] in
lemma put_norm_le (i : Grade d) (x : V i) : ‖put V i x‖ ≤ ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).2
  intro j; rcases eq_or_ne j i with rfl|he
  · rw [put,Pi.single_eq_same]
  rw [put,Pi.single_eq_of_ne he,norm_zero]; exact norm_nonneg _

omit [∀ i, NormedSpace ℂ (V i)] in
theorem by_grade (x : Col V) : ∑ i, put V i (x i) = x := by
  funext i
  rw [Finset.sum_apply]
  exact (Finset.sum_eq_single i (fun j _ hj=> Pi.single_eq_of_ne hj.symm _) (by simp)).trans (Pi.single_eq_same ..)

def onFlag (i : Grade d) (x : Col V) := ∀ j, i < j → x j = 0

def flag (i : Grade d) : Submodule ℂ (Col V) where
  carrier := { x | onFlag V i x }
  add_mem' h k j hj := by simp [Pi.add_apply, h j hj, k j hj]
  zero_mem' _ _ := rfl
  smul_mem' c _ h j hj := by simp [Pi.smul_apply, h j hj]

def onPrev (i : Grade d) (x : Col V) := ∀ j, i ≤ j → x j = 0

def prev (i : Grade d) : Submodule ℂ (Col V) where
  carrier := {x | onPrev V i x}
  add_mem' h k j hj := by simp [Pi.add_apply, h j hj, k j hj]
  zero_mem' _ _ := rfl
  smul_mem' c _ h j hj := by simp [Pi.smul_apply, h j hj]

lemma triangular_iff_stays (A : BlockMatrix V) : triangular V A ↔
    ∀ i (x : Col V), x ∈ flag V i → A x ∈ flag V i := by
  refine ⟨fun h i x hx j hj => ?_, fun h i j hij x => ?_⟩
  · rw [← by_grade V x, map_sum, Finset.sum_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases he : k ≤ i
    · exact h j k (lt_of_le_of_lt he hj) _
    rw [show x k = 0 from hx (j:=k) (lt_of_not_ge he)] -- binder explicit?
    simp [put]
  exact h j _ (show put V j x ∈ flag V j from
    fun k hk => Pi.single_eq_of_ne (ne_of_gt hk) _) i hij

variable {V}
lemma triangular.prev {A : BlockMatrix V} (h : triangular V A) (i : Grade d) (x : Col V)
    (hx : x ∈ prev V i) : A x ∈ prev V i := by
  intro j hj
  rw [← by_grade V x,map_sum,Finset.sum_apply]; refine Finset.sum_eq_zero fun k _ => ?_
  by_cases he : k < i
  · exact h j k (he.trans_le hj) (x k)
  rw [show x k=0 from hx k (le_of_not_gt he)]; simp [put]

lemma triangular.comp {A B : BlockMatrix V} (h : triangular V A) (he : triangular V B) :
    triangular V (A.comp B) := by
  rw [triangular_iff_stays] at *
  intro i x hx; exact h i _ (he i _ hx)

lemma triangular.inv [FiniteDimensional ℂ (Col V)] {A : Col V ≃ₗ[ℂ] Col V}
    (h : triangular V A.toLinearMap) : triangular V A.symm.toLinearMap := by
  rw [triangular_iff_stays] at *
  intro i x hx
  let f := A.toLinearMap.restrict (h i)
  have h₁ : Injective f := by intro a b hab; exact Subtype.ext (A.injective (congr_arg Subtype.val hab))
  obtain ⟨y,hy⟩ := (LinearMap.injective_iff_surjective.mp h₁) (⟨x,hx⟩ : flag V i)
  change A.symm x ∈ _
  rw [← (show A y.val = x from congr_arg Subtype.val hy),LinearEquiv.symm_apply_apply]
  exact y.property

lemma zero_block (A : BlockMatrix V) (i j : Grade d) : block V A i j 0 = 0 := by
  simp [block, put]

lemma block_sum (A : BlockMatrix V) (i : Grade d) (x : Col V) :
    A x i = ∑ j, block V A i j (x j) := by
  conv_lhs => rw [← by_grade V x, map_sum,Finset.sum_apply]

lemma same_diag {A : BlockMatrix V} (h : triangular V A) {i : Grade d} {x : Col V}
    (hx : x ∈ flag V i) : A x i = block V A i i (x i) := by
  rw [block_sum]; refine Finset.sum_eq_single i (fun j _ hj=> ?_) (by simp)
  rcases lt_or_gt_of_ne hj with he|he
  · exact h i j he _
  rw [show x j = 0 from hx j he,zero_block]

lemma put_flag (i : Grade d) (j : Grade d) (x : V j) (hj : j ≤ i) : put V j x ∈ flag V i :=
  fun _ hk => Pi.single_eq_of_ne (ne_of_gt (lt_of_le_of_lt hj hk)) x

lemma inv_diag [FiniteDimensional ℂ (Col V)] {A : Col V ≃ₗ[ℂ] Col V} (h : triangular V A.toLinearMap)
    (i : Grade d) (x : V i) : block V A.toLinearMap i i (block V A.symm.toLinearMap i i x) = x := by
  rw [show block V A.toLinearMap i i (block V A.symm.toLinearMap i i x)=A (A.symm (put V i x)) i from
    (same_diag h ((triangular_iff_stays _ _).1 h.inv i _ (put_flag i i x le_rfl))).symm,
    LinearEquiv.apply_symm_apply]; exact Pi.single_eq_same ..
end YM.RG12.Frames
