import YM.RG02.Wick.Drivers

/-! Bound on number of uncharged legs on a connected vacuum driver. Uses
the actual parity of the graph and `NoCut`, only in the sector of fixed
logical tag where stochastic obligations impose no other connections. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG02.Shear
open MvPolynomial Finset Next.Rank Next.Rank.Normal Function Wick Marker Marks Multi
open scoped Classical BigOperators
variable {I A V : Type}[DecidableEq I]

lemma grow_at (t : Finset I)(s : Finset A)(E:A→ Finset I)
    (h : NoCut t (fun i j => ∃ a∈s, i∈E a ∧ j∈E a))(ht : ∀ a∈s, (E a).card ≤ 2) : t.card ≤ s.card+1 := by
   classical
   by_cases he : t.Nonempty; swap; · simp [not_nonempty_iff_eq_empty.mp he]
   obtain ⟨i,hi⟩:=he
   suffices H : ∀ U ⊆ s, ∀ W : Finset I, i∈W → W⊆t → W.card=U.card+1 → (∀ a∈U,E a⊆W) → t.card≤s.card+1 from H ∅ (empty_subset _) {i} (mem_singleton_self i) (singleton_subset_iff.mpr hi) (by simp) (by simp)
   have hr k : ∀ U ⊆ s, (s\U).card=k → ∀ W : Finset I,i∈W → W⊆t → W.card=U.card+1 → (∀ a∈U,E a⊆W) → t.card≤s.card+1 := by
      induction k with
      | zero =>
         intro S hs H W hW hw hc he; by_cases h0:W=t
         · subst W; rw [hc]; gcongr
         obtain ⟨l,hl,y,hy,a,ha,hg,hx⟩ := h W hw ⟨_,hW⟩ (Finset.sdiff_nonempty.mpr <| fun ht=>h0 (Finset.Subset.antisymm hw ht))
         · have hm := Finset.mem_sdiff.mpr ⟨ha,show a∉S from fun HH => (mem_sdiff.mp hy).2 (he a HH hx)⟩
           rw [card_eq_zero.mp H] at hm; exact False.elim (notMem_empty _ hm)
      | succ k ih =>
         intro S hs H W hW hw hc he; by_cases h0:W=t
         · subst W; rw [hc]; gcongr
         obtain ⟨l,hl,y,hy,a,ha,hg,hx⟩ := h W hw ⟨_,hW⟩ (Finset.sdiff_nonempty.mpr <| fun ht=>h0 (Finset.Subset.antisymm hw ht))
         obtain ⟨hu,hJ⟩ := mem_sdiff.mp hy
         have ha' : a∉ S:= fun HH => hJ (he a HH hx)
         refine ih (insert a S) (insert_subset ha hs) ?_ (insert y W) (mem_insert_of_mem hW) (insert_subset hu hw) ?_ ?_
         · rw [card_sdiff_of_subset hs] at H; rw [card_sdiff_of_subset (insert_subset ha hs),card_insert_of_notMem ha']; omega
         · rw [card_insert_of_notMem hJ,hc,card_insert_of_notMem ha']
         intro b hh; rcases mem_insert.mp hh with hh|HH
         · subst b
           rw [show E a = {l,y} from (Finset.eq_of_subset_of_card_le (insert_subset hg (singleton_subset_iff.mpr hx)) (by rw [card_pair (ne_of_mem_of_not_mem hl hJ)]; exact ht a ha)).symm];
           exact insert_subset (mem_insert_of_mem hl) (singleton_subset_iff.mpr (mem_insert_self ..))
         exact (he b HH).trans (subset_insert ..)
   exact fun U HU => hr _ U HU rfl

open Wick.Actor
-- Trivial tag; integrate after choosing true branch.
abbrev Dot := Draw (fun _ : Unit=>Unit)

def dot := expectation fun (_:Unit) (_:Unit) => (1:ℂ)
@[simp] lemma choose_dot : Multiplying dot := contracting _ (by simp)

variable [DecidableEq A][Fintype A] {T : Census I}[Fintype I]
lemma pins (q : Symmetric V)(ℓ:A→V) (o : A→I)(x:I→ℂ)(s : T.Mode)(p:(Lines A).Mode)
    (H : (Extra.Trajectories.connected (Wick.terms o (fun i (_ : Dot)=>x i) (Wick.edges (fun _=>q) (fun _=>ℓ)) dot)).part (Pair.mk s p)≠0)
    : s.val.card≤p.val.card+1 ∧ (arms o s.val).card=p.val.card*2 := by
   let y := Wick.terms o (fun i (_ : Dot)=>x i) (Wick.edges (fun _=>q) (fun _=>ℓ)) dot (R:=T)
   have he (i:I) : Actor.Needs (fun _ : Dot=>x i) ∅ := fun _ _ _ => rfl
   have hv (i:Multi.Hot (full A)) : Actor.Needs (Wick.edges (T:=Dot) (fun _=>q) (fun _=>ℓ) i) (∅:Finset Unit) := fun _ _ _ => rfl
   obtain ⟨hc,hg⟩ := Wick.only_jointly o p choose_dot he hv s H
   unfold Paired at hc; rw [Pair.fst_mk,Pair.snd_mk] at hc
   constructor
   · apply grow_at s.val p.val (paidFor o) _ (fun a ha=>?_)
     · intro V HV hv hd; obtain ⟨i,hi,j,hj,HL⟩ := hg V HV hv hd; exact ⟨i,hi,j,hj,HL.resolve_right fun H=> by apply H; apply disjoint_left.mpr; intro v k; simp [budget] at k⟩
     exact (card_image_le).trans (hc.2 a ha).le
   calc
      _ = ∑ i∈p.val, i.sites.card := by rw [← hc.1]; exact Finset.card_biUnion (parts_wise ..)
      _ = ∑ _∈p.val, 2 := sum_congr rfl fun i hi => hc.2 i hi
      _ = _ := by simp
end YM.RG02.Shear
