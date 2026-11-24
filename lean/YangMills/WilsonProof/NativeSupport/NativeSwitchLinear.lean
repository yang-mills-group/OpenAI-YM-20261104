import YangMills.WilsonProof.NativeSupport.FundedProjection

/-! Exact linear term of the native mounted switch. All original numerical
scores are held fixed. A separate one-generator census reads each single
switch, regardless of the degree of the marker carried by that switch. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.NativeSwitch
open Finset Marker Merge.Switch Extra.Trajectories
open scoped BigOperators Classical
variable {I V : Type} [Fintype I] [DecidableEq I] [DecidableEq V] {B : Census V}

def singleProbe (i j : I) : Poly (Stock.census Unit) :=
  if j=i then Poly.send ((Stock.census Unit).fire ()) 1 else 0

theorem single_score (f : Ways I) (i : I) :
    (sound (singleProbe i) f).part ((Stock.census Unit).fire ()) = (jet f {i} : ℂ) := by
  rw [sound,mapScores_apply,Poly.part_sum,sum_eq_single {i}]
  · rw [prod_singleton,singleProbe,if_pos rfl,Poly.part_smul,Poly.part_send,if_pos rfl,mul_one]
  · intro D _ hD
    by_cases e : D=∅
    · subst D
      rw [prod_empty,Poly.part_smul,Poly.one_part,if_neg ((Stock.census Unit).fire_hot ()),mul_zero]
    · obtain ⟨j,hj,ne⟩ : ∃ j∈D, j≠i := by
        by_contra! every
        obtain ⟨j,hj⟩ := nonempty_iff_ne_empty.mpr e
        apply hD
        apply subset_antisymm
        · intro k hk; exact mem_singleton.mpr (every _ hk)
        · exact singleton_subset_iff.mpr (every _ hj ▸ hj)
      have z : (∏ j∈D,singleProbe i j)=0 := prod_eq_zero hj (if_neg ne)
      rw [z,smul_zero,Poly.part_nil]
  · simp

omit [Fintype I] in
private lemma scaled_product (r : I→Poly B) (b : ℂ) (D : Finset I) :
    (∏ j∈D, b • r j) = b^D.card • ∏ j∈D, r j := by
  induction D using Finset.induction_on with
  | empty => simp
  | @insert i D hi ih =>
    rw [prod_insert hi,ih,prod_insert hi,smul_mul_smul_comm,card_insert_of_notMem hi,pow_succ,mul_comm b]

private lemma singles (r : I→Poly B) (f : Ways I) :
    (∑ D : Finset I, if D.card=1 then (jet f D : ℂ) • ∏ j∈D,r j else 0) =
      ∑ i, (sound (singleProbe i) f).part ((Stock.census Unit).fire ()) • r i := by
  simp_rw [single_score]
  rw [← sum_filter]
  symm
  apply sum_bij (fun i _ => {i})
  · intro i _; simp
  · intro i _ j _ e; exact singleton_injective e
  · intro D hD
    obtain ⟨i,hi⟩ := card_eq_one.mp (mem_filter.mp hD).2
    exact ⟨i,mem_univ _,hi.symm⟩
  · intro i _; simp

theorem dilation (r : I→Poly B) (f : Ways I) (b : ℂ) :
    sound (fun i => b • r i) f =
      (jet f ∅ : ℂ) • 1 +
      b • (∑ i, (sound (singleProbe i) f).part ((Stock.census Unit).fire ()) • r i) +
      b^2 • (∑ D : Finset I, if 2≤D.card then
        b^(D.card-2) • ((jet f D : ℂ) • ∏ j∈D,r j) else 0) := by
  rw [← singles r f,sound,mapScores_apply]
  have c : (jet f ∅ : ℂ) • (1 : Poly B) =
      ∑ D : Finset I, if D.card=0 then (jet f D : ℂ) • ∏ j∈D,r j else 0 := by
    simp [card_eq_zero]
  rw [c,Finset.smul_sum,Finset.smul_sum,← sum_add_distrib,← sum_add_distrib]
  apply sum_congr rfl
  intro D _
  rw [scaled_product]
  rcases eq_or_ne D.card 0 with h|h
  · simp [h]
  rcases eq_or_ne D.card 1 with h'|h'
  · simp only [h',one_ne_zero,if_false,if_true,pow_one,zero_add,show ¬2≤1 by omega,smul_zero,add_zero]
    exact smul_comm _ _ _
  have ge : 2≤D.card := by omega
  simp only [if_neg h,if_neg h',if_pos ge,smul_zero,add_zero,zero_add,smul_smul]
  rw [← mul_assoc,← pow_add,show 2+(D.card-2)=D.card by omega,mul_comm]

end YM.Integration.InletSusceptibility.NativeSwitch
