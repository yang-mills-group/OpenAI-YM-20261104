import YM.OPE.Nesting.Endpoint

/-! A first signed replacement in a finite OPE contraction. The common
absolute price is multiplied once per factor. The discrepancies add. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredNestedProducts
open Finset
open scoped BigOperators Classical

structure Priced (x y : ℂ) (B E : ℝ) : Prop where
  left : ‖x‖ ≤ B
  right : ‖y‖ ≤ B
  change : ‖x - y‖ ≤ B * E

namespace Priced
variable {x y z w : ℂ} {A B E D : ℝ}

theorem nonneg (h : Priced x y A E) : 0 ≤ A :=
  (norm_nonneg _).trans h.left

theorem expand (h : Priced x y A E) (ab : A ≤ B) (ep : 0 ≤ E) : Priced x y B E :=
  ⟨h.left.trans ab,h.right.trans ab,h.change.trans (mul_le_mul_of_nonneg_right ab ep)⟩

theorem mul (h : Priced x y A E) (k : Priced z w B D) :
    Priced (x*z) (y*w) (A*B) (E+D) := by
  constructor
  · simpa only [norm_mul] using mul_le_mul h.left k.left (norm_nonneg _) h.nonneg
  · simpa only [norm_mul] using mul_le_mul h.right k.right (norm_nonneg _) h.nonneg
  calc
    ‖x*z - y*w‖ = ‖(x-y)*z + y*(z-w)‖ := by congr 1; ring
    _ ≤ ‖x-y‖*‖z‖ + ‖y‖*‖z-w‖ := by simpa only [norm_mul] using norm_add_le ((x-y)*z) (y*(z-w))
    _ ≤ (A*E)*B + A*(B*D) := add_le_add
      (mul_le_mul h.change k.left (norm_nonneg _) ((norm_nonneg _).trans h.change))
      (mul_le_mul h.right k.change (norm_nonneg _) h.nonneg)
    _ = _ := by ring

theorem product {ι : Type*} (t : Finset ι) (x y : ι → ℂ) (B E : ι → ℝ)
    (h : ∀ i∈t, Priced (x i) (y i) (B i) (E i)) :
    Priced (∏ i∈t,x i) (∏ i∈t,y i) (∏ i∈t,B i) (∑ i∈t,E i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp only [Finset.prod_empty,Finset.sum_empty]; exact ⟨by simp,by simp,by simp⟩
  | @insert a t ha ih =>
    simpa only [Finset.prod_insert ha,Finset.sum_insert ha] using
      (h a (mem_insert_self a t)).mul (ih (fun i hi=>h i (mem_insert_of_mem hi)))

theorem terms {ι : Type*} [Fintype ι] (x y : ι → ℂ) (B E : ℝ)
    (h : ∀ i, Priced (x i) (y i) B E) :
    Priced (∑ i,x i) (∑ i,y i) ((Fintype.card ι:ℝ)*B) E := by
  constructor
  · exact (norm_sum_le _ _).trans (by simpa using sum_le_sum (fun i (_ : i∈(univ : Finset ι))=>(h i).left))
  · exact (norm_sum_le _ _).trans (by simpa using sum_le_sum (fun i (_ : i∈(univ : Finset ι))=>(h i).right))
  rw [← sum_sub_distrib]
  exact (norm_sum_le _ _).trans (by simpa only [sum_const,card_univ,nsmul_eq_mul,mul_assoc] using
    (sum_le_sum (fun i (_ : i∈(univ : Finset ι))=>(h i).change)))
end Priced
end YM.Integration.WilsonCenteredNestedProducts
