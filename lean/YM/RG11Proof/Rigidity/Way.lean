import YM.RG11Proof.Rigidity.FuseLine

/-!
# Allowed configurations for panel deletions
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Rigidity
open palette Maxwell.Free Function
open scoped BigOperators Classical

-- list of all panel endpoints
variable {Q X : Type}
def stroll (whereAt : Q→X) (L : List (Pair Q)) := L.flatMap fun i=> [whereAt i.1,whereAt i.2]

@[simp] lemma stroll_cons (whereAt : Q→X) (L : List (Pair Q)) i :
    stroll whereAt (i::L)=whereAt i.1::whereAt i.2::stroll whereAt L := rfl

structure Journey (w : Q→X) (S : Finset X) (L : List (Pair Q)) : Prop where
  nodup : (stroll w L).Nodup
  safe a : a∈stroll w L → a∉S

lemma legJourney [DecidableEq X] (w : Q→X) (S : Finset X) (i : Pair Q) (L) : Journey w S (i::L) ↔
    w i.1 ≠ w i.2 ∧ w i.1∉S ∧ w i.2∉S ∧ Journey w (insert (w i.2) (insert (w i.1) S)) L := by
  constructor
  · intro h
    have ht := h.nodup; simp only [stroll_cons,List.nodup_cons,List.mem_cons,not_or] at ht
    refine ⟨ht.1.1,h.safe _ (by simp),h.safe _ (by simp),ht.2.2,fun a ha=> ?_⟩
    have := h.safe a (by simp [ha])
    simp; exact ⟨fun he=>ht.2.1 (he ▸ ha),fun he=>ht.1.2 (he ▸ ha),this⟩
  rintro ⟨h,ht,hu,hL⟩
  constructor
  · simp only [stroll_cons,List.nodup_cons,List.mem_cons,not_or]
    exact ⟨⟨h,fun hi=> hL.safe _ hi (by simp)⟩,fun hi=> hL.safe _ hi (by simp),hL.nodup⟩
  intro a ha
  simp only [stroll_cons,List.mem_cons] at ha
  rcases ha with rfl|rfl|ha
  · exact ht
  · exact hu
  exact fun hi=> hL.safe _ ha (by simp [hi])

lemma convertWalk {S : Finset E4} {L : List Crowd.Panel} : Journey Prod.snd S L ↔ Walks S L := by
  classical
  induction L generalizing S with
  | nil => exact iff_of_true ⟨List.nodup_nil,by simp [stroll]⟩ trivial
  | cons a l ih => rw [legJourney,ih,Walks]

lemma Journey.weaken {w : Q→X} {S V : Finset X} (hv : S⊆V) {L} (h : Journey w V L) : Journey w S L :=
    ⟨h.nodup,fun _ ha hx=>h.safe _ ha (hv hx)⟩
lemma Journey.perm {w : Q→X} {S : Finset X} {L P} (h : Journey w S L) (ht : List.Perm P L) : Journey w S P := by
  have he : List.Perm (stroll w P) (stroll w L) := List.Perm.flatMap_right _ ht
  exact ⟨he.nodup_iff.mpr h.nodup,fun _ ha=> h.safe _ (he.mem_iff.mp ha)⟩

lemma pickJourney {w : Q→X} {S : Finset X} {P : List (Pair Q)} (h : Journey w S P) (i : Fin P.length) :
    Journey w S (P.get i :: P.eraseIdx i.val) := h.perm (by simpa using List.getElem_cons_eraseIdx_perm (l:=P) i.isLt)

-- Merge after a single pull, sparing one endpoint on each panel in either
-- choice while the other two are removed.
lemma mergeWay {w : Q→X} {S : Finset X} (u v : Pair Q) (U V : Q)
    (hu : U=u.1 ∨ U=u.2) (hv : V=v.1 ∨ V=v.2) (p : List (Pair Q)) (h : Journey w S (u::v::p)) :
    Journey w S ((U,V)::p) := by
  have ht : List.Sublist (stroll w ((U,V)::p)) (stroll w (u::v::p)) := by
    rcases hu with rfl|rfl <;> rcases hv with rfl|rfl
    all_goals simp only [stroll_cons]; repeat' (first | apply List.Sublist.cons_cons | apply List.Sublist.cons | rfl) -- cons_cons greedy may hit duplicate
  exact ⟨h.nodup.sublist ht,fun _ ha=> h.safe _ (ht.subset ha)⟩

end YM.RG11.Rigidity
