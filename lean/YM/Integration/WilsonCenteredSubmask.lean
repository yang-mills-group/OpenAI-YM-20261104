import YM.Integration.WilsonCenteredHardPartitions

/-! Restrict one complete enrolled marked polynomial to the subwords of its
captured mask. The operation commutes with multiplication and keeps the
original vacuum coefficient. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredSubmask
open Finset Marker
open scoped Classical BigOperators
variable {V : Type} [DecidableEq V] {R : Census V}

def cut (s : R.Mode) (A : Poly R) : Poly R := Poly.inject (fun t=>if t.val⊆s.val then A.part t else 0)

@[simp] theorem tested (s t : R.Mode) (A : Poly R) :
    (cut s A).part t = if t.val⊆s.val then A.part t else 0 :=rfl

theorem product (s : R.Mode) (A B : Poly R) : cut s (A*B)=cut s A*cut s B :=by
  ext t
  simp only [tested,Poly.part_mul]
  by_cases lives : t.val⊆s.val
  · rw [if_pos lives]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    by_cases joined : Poly.merges i j t
    · have a : i.val⊆s.val := subset_union_left.trans (joined.2 ▸ lives)
      have b : j.val⊆s.val := subset_union_right.trans (joined.2 ▸ lives)
      simp [joined,a,b]
    simp [joined]
  rw [if_neg lives]
  symm
  apply sum_eq_zero; intro i _
  apply sum_eq_zero; intro j _
  by_cases joined : Poly.merges i j t
  · by_cases a : i.val⊆s.val
    · have b : ¬ j.val⊆s.val := fun h => lives (joined.2 ▸ union_subset a h)
      simp [joined,b]
    simp [joined,a]
  simp [joined]

theorem unit (s : R.Mode) : cut s (1:Poly R)=1 :=by
  ext t
  rw [tested]
  by_cases ht : t=R.quiet
  · subst t
    simp [Census.quiet]
  simp [Poly.one_part,ht]

def hom (s : R.Mode) : Poly R →+* Poly R where
  toFun := cut s
  map_one' := unit s
  map_mul' := product s
  map_zero' := by ext t; simp
  map_add' a b := by ext t; by_cases h : t.val⊆s.val <;> simp [h]

theorem kept (s : R.Mode) (A : Poly R) : (cut s A).part s=A.part s :=by simp

theorem vacuum (s : R.Mode) (A : Poly R) : (cut s A).part R.quiet=A.part R.quiet :=by simp [Census.quiet]

end YM.Integration.WilsonCenteredSubmask
