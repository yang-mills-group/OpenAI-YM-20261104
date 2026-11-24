import YM.Integration.WilsonCenteredSubmask

/-! Mark any subset of the original eligible hard owners at the actual
capture. Every quiet factor outside that subset keeps its original value. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredOccupiedFamilies
open Finset Marker WilsonCenteredSubmask
open scoped Classical BigOperators
variable {V J : Type} [DecidableEq V] [DecidableEq J] {R : Census V}

/-- All occupied faces of one original owner inside the requested mask. -/
def dye (s : R.Mode) (A : Poly R) := cut s A - A.part R.quiet • (1:Poly R)

theorem quiet (s : R.Mode) (A : Poly R) : (dye s A).part R.quiet=0 := by
  change (cut s A).part R.quiet - (A.part R.quiet • (1:Poly R)).part R.quiet=0
  rw [vacuum,Poly.part_smul,Poly.one_part,if_pos rfl,mul_one,sub_self]

theorem marked (s t : R.Mode) (A : Poly R) (hot : t≠R.quiet) :
    (dye s A).part t=if t.val⊆s.val then A.part t else 0 :=by
  change (cut s A).part t - (A.part R.quiet • (1:Poly R)).part t=_
  rw [tested,Poly.part_smul,Poly.one_part,if_neg hot,mul_zero,sub_zero]

theorem absolute (s : R.Mode) (A : Poly R) (w : V→ℝ) (hw : ∀v,0<w v) :
    Poly.price w (dye s A)≤Poly.price w A :=by
  unfold Poly.price
  apply sum_le_sum
  intro t _
  apply mul_le_mul_of_nonneg_left _ (Poly.worth hw _).le
  by_cases hot : t=R.quiet
  · subst t;rw [quiet,norm_zero];exact norm_nonneg _
  rw [marked s t A hot]
  split
  · exact le_rfl
  · rw [norm_zero];exact norm_nonneg _

theorem vanish (F : Finset J) (B : J→Poly R) (hB : ∀j,(B j).part R.quiet=0)
    (s : R.Mode) (many : s.val.card < F.card) : (∏j∈F,B j).part s=0 := by
  induction F using Finset.induction_on generalizing s with
  | empty => simp at many
  | @insert j F hj ih =>
    rw [prod_insert hj,Poly.part_mul]
    apply sum_eq_zero; intro a _
    apply sum_eq_zero; intro b _
    by_cases split : Poly.merges a b s
    · rw [if_pos split]
      by_cases idle : a=R.quiet
      · rw [idle,hB,zero_mul]
      have some : a.val.Nonempty :=by
        by_contra h
        exact idle (Subtype.ext (not_nonempty_iff_eq_empty.mp h))
      have size : a.val.card+b.val.card=s.val.card :=
        (card_union_of_disjoint split.1).symm.trans (congrArg card split.2)
      rw [card_insert_of_notMem hj] at many
      have smaller : b.val.card < F.card:=by have := some.card_pos; omega
      rw [ih b smaller,mul_zero]
    simp [split]

private theorem vacuum_product (F : Finset J) (v : J→ℂ) :
    (∏j∈F,v j • (1:Poly R))=(∏j∈F,v j) • (1:Poly R) := by
  induction F using Finset.induction_on with
  | empty => simp
  | @insert j F hj ih =>
    rw [prod_insert hj,prod_insert hj,ih,smul_mul_assoc,one_mul,smul_smul]

theorem original (F : Finset J) (H : J→Poly R) (s : R.Mode) :
    (∏j∈F,H j).part s =
      ∑ I∈F.powerset.filter (fun I=>I.card≤s.val.card),
        (∏j∈F\I,(H j).part R.quiet) * (∏j∈I,dye s (H j)).part s := by
  let q j := (H j).part R.quiet
  have crossed : (∏j∈F, (dye s (H j)+q j • (1:Poly R)))=cut s (∏j∈F,H j) :=by
    simp only [dye,q,sub_add_cancel]
    exact (map_prod (hom s) H F).symm
  rw [←kept s (∏j∈F,H j),←crossed,prod_add,Poly.part_sum]
  rw [sum_filter]
  apply sum_congr rfl
  intro I _
  rw [vacuum_product,mul_smul_comm,mul_one,Poly.part_smul]
  by_cases h : I.card≤s.val.card
  · simp only [if_pos h,q]
  have off:=vanish I (fun j=>dye s (H j)) (fun j=>quiet s _) s (lt_of_not_ge h)
  simp only [if_neg h,off,mul_zero]

end YM.Integration.WilsonCenteredOccupiedFamilies
