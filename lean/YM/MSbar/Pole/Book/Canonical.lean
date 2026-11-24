import YM.MSbar.Pole.Book.Pairing
/-! # Take momentum and derivative evaluation on conserving inputs -/
noncomputable section
set_option autoImplicit false
namespace YM.MSbar.Pole.Book
open Function Set Filter MeasureTheory Momentum Ambient Age Mellin place Symbol Sew Thread Feynman District
open scoped Topology ContDiff BigOperators Classical InnerProductSpace
variable {I : Type} [Fintype I] {M R:Finset I} {i:I}
lemma acts (F:Cloud I) {a} (h:Local M a F) (L : ∀ n,External I n→L[ℝ] External I n) (ht:Tensor (fun n x=>F n (L n x))) (hp:∀ r n x, L n (move M r x)= move M r (L n x)) : Local M a (fun n x=>F n (L n x)) := by
  refine ⟨⟨ht, fun n => ?_⟩,fun ha=>?_,fun n x t ht=>?_⟩
  · have he:=(Wall.affine (h.regular.constant (U:=Set.univ) |>.budget n) (L n) 0).fixed (mem_univ (0:ℂ))
    simpa only [zero_add] using! he
  · funext n x; change F n _=_; rw [h.trivial ha]; rfl
  rw [hp]; exact h.weights _ _ _ ht -- fix
lemma fixed_frame (F:Cloud I) {a} (h:Local M a F) (hp:R ⊆ M) (hi:i∈R) : Local M a (fun n x=>F n (Tip.anchor R i x)):= by
  set G : ∀ n : ℕ, External I n →L[ℝ] External I n:=Tip.bead R i with hG
  simp_rw [← Tip.beads]; refine acts F h G ?_ ?_
  · have hh (n m:ℕ) (x:External I n)(T:place n →L[ℝ]place m): G m (T ∘ x)=T∘ G n x:= by
      simp_rw [hG,Tip.beads]; unfold Tip.anchor; ext1 j; by_cases hv:j=i
      · subst j; simp
      simp [hv]
    constructor
    · intro n J x; rw [show G n (J∘x)= J∘ G n x from hh n n x J.toLinearIsometry.toContinuousLinearMap,h.regular.1.moves]
    intro n x; rw [hh,h.regular.1.agrees]
  intro r n x; simp_rw [hG,Tip.beads]; unfold Tip.anchor; ext1 j; by_cases hv:j=i
  · subst j
    unfold move; rw [update_self,if_pos (hp hi),update_self,smul_neg,Finset.smul_sum]; congr 1; exact Finset.sum_congr rfl fun i hi=> if_pos (hp (Finset.mem_of_mem_erase hi))
  unfold move; rw [update_of_ne hv,update_of_ne hv]

lemma linear_at {F:Cloud I} {V:Finset I} (hf:Shape (R∪V) V F) (hp:Disjoint V R) (hi:i∈R):
    Shape (R.erase i∪V) V (fun n x=> F n (Tip.anchor R i x)) := by
  constructor
  · intro n x y hx; apply hf.sees; intro j hj; unfold Tip.anchor; by_cases he:j=i
    · rw [he,update_self,update_self]; congr 1; exact Finset.sum_congr rfl fun v hv=>hx v (Finset.mem_union_left _ hv)
    rw [update_of_ne he,update_of_ne he]; apply hx; simp only [Finset.mem_union,Finset.mem_erase] at *; tauto
  intro j hj n x
  have ha : j∉ R:=fun hh=> Finset.disjoint_left.mp hp hj hh
  have ht : j≠i:= Ne.symm (ne_of_mem_of_not_mem hi ha)
  have hx v : Tip.anchor R i (update x j v)=update (Tip.anchor R i x) j v:=by
    unfold Tip.anchor
    rw [show ∑ k∈R.erase i,update x j v k=∑ k∈R.erase i,x k from Finset.sum_congr rfl fun k hk=> update_of_ne (ne_of_mem_of_not_mem (Finset.mem_of_mem_erase hk) ha) _ _,update_comm ht]
  simp_rw [hx]; exact hf.angle j hj ..
end YM.MSbar.Pole.Book
