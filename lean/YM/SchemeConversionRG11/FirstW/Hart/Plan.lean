import YM.SchemeConversionRG11.FirstW.Hart.Breathe
import YM.Next.RANK.Keys
/-! Discrete Secure signs on signed chart slope with powerset-difference convention. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.FirstW
open Function Lattice Pert Align Topology Maxwell Filter Next.Rank.CellsInt
open scoped BigOperators Classical
variable {X E : Type*} [AddCommGroup X] [One X] [NormedAddCommGroup E] [NormedSpace ℝ E] {j : ℕ}
omit [NormedSpace ℝ E] in
lemma jumps_eq (a : Fin j→Axis) (f : Cover→E) : jumps j a f=combine (List.ofFn a) f := by
  induction j generalizing f with
  | zero=> simp [jumps,combine]
  | succ j ih=>
    rw [List.ofFn_succ, jumps]; rw [ih]; exact combine_up .. -- check
-- subset generation equivalence
private def shootS {n : ℕ} (q : Finset (Fin n)) := q.image Fin.succ
private lemma green (q : Finset (Fin j)) : 0 ∉ shootS q := by simp [shootS]
private lemma ripe (s : Finset (Fin (j+1))) (hx:0∉s) : ∃ t:Finset (Fin j), shootS t=s := by
   refine ⟨Finset.univ.filter fun v=>v.succ∈s,?_⟩; ext i; cases i using Fin.cases <;> simp [shootS,hx] -- hx sign
private lemma shoots (t u:Finset (Fin j)) (h : shootS t=shootS u): t=u := by
  ext i; have hh : i.succ∈shootS t↔i.succ∈shootS u:=by rw [h]
  simpa [shootS] using hh
private def paired (p : Bool× Finset (Fin j)): Finset (Fin (j+1)) := if p.1 then insert 0 (shootS p.2) else shootS p.2
private lemma both (j : ℕ): Bijective (@paired j) := by
  constructor
  · rintro ⟨b,t⟩ ⟨c,u⟩ h
    cases b <;> cases c <;> dsimp [paired] at h
    · congr 1; exact shoots _ _ h
    · exact False.elim (green t (h.symm ▸ Finset.mem_insert_self 0 (shootS u)))
    · exact False.elim (green u (h ▸ Finset.mem_insert_self 0 (shootS t)))
    · congr 1; apply shoots; rw [← Finset.erase_insert (green t),h, Finset.erase_insert (green u)]
  intro s; by_cases H:0∈s
  · obtain ⟨q,hq⟩ := ripe (s.erase 0) (Finset.notMem_erase _ _); exact ⟨(true,q),show _ from by simp [paired,hq,Finset.insert_erase H]⟩
  obtain ⟨q,rfl⟩ := ripe s H; exact ⟨(false,q),rfl⟩
lemma jumps_supply (j : ℕ) (a : Fin j→Axis) (p : Cover→E) (x : Cover) : jumps j a p x= ∑ s:Finset (Fin j), Bare.sign s • p (x+∑ i∈s,step (a i)) := by
  induction j generalizing p x with
  | zero=>
     simp_rw [jumps]; rw [Finset.sum_eq_single_of_mem (∅:Finset (Fin 0)) (Finset.mem_univ _)]; · simp [Bare.sign]
     intro a _ ha; exact False.elim (ha (Subsingleton.elim ..))
  | succ j ih=>
    let f (s:Finset (Fin (j+1))) := Bare.sign s • p (x+∑ i∈s, step (a i)); change _=∑ s,f s
    rw [← Equiv.sum_comp (Equiv.ofBijective (@paired j) (both j)) f]
    change _=∑ q : (Bool × Finset (Fin j)),f (paired q)
    rw [Fintype.sum_prod_type,Fintype.sum_bool,← Finset.sum_add_distrib,jumps,ih]; apply Finset.sum_congr rfl; intro t _
    unfold paired f; simp only [↓reduceIte,Bool.false_eq_true]
    rw [Bare.sign_eq, Bare.sign_eq,Bare.sign_eq, Finset.card_insert_of_notMem (green t), Finset.sum_insert (green t), shootS,Finset.sum_image,Finset.card_image_of_injective _ (Fin.succ_injective _)]
    dsimp only [Fin.tail,stepValue]; ring_nf
    have he : t.card ≤ j := by simpa using Finset.card_le_card (Finset.subset_univ t)
    rw [show 1+j-(1+t.card)=(j-t.card) by omega, show 1+j-t.card=j-t.card+1 by omega,pow_succ]; simp [sub_eq_add_neg]
    exact (Fin.succ_injective j).injOn
end YM.RG11.FirstW
