import YM.Space.Configurations

/-!
# Geometry for all finite ensembles

Use a single universal alphabet `ℕ` for slots. Nonempty clusters carry their own
 index sets and can be permuted arbitrarily; always work with finite ensembles,
 never interpreting countably many physical fields in a reading.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet
open Function Finset Set
open scoped Topology BigOperators Classical
abbrev Slot:= ℕ
-- nonempty block
abbrev Pod := {s:Finset Slot // s.Nonempty}
namespace Pod
def seed (i:Slot) : Pod:= ⟨{i},Finset.singleton_nonempty i⟩
abbrev here (p:Pod):= p.val.min' p.property
theorem here_mem (p:Pod): p.here∈ p.val:= Finset.min'_mem ..
abbrev card (p:Pod):=p.val.card
lemma card_pos (p: Pod):0 < p.card:=Finset.card_pos.mpr p.property
lemma le_set (p q:Pod) : p≤q↔p.val⊆q.val:= Iff.rfl
lemma lt_card {p q:Pod}(h:p<q): p.card<q.card:= Finset.card_lt_card h
lemma card_seed (i:Slot):(seed i).card=1:=Finset.card_singleton _
lemma le_seed {p:Pod}{i:Slot}(h:p ≤ seed i): p=seed i:=by
   apply le_antisymm h; exact Finset.singleton_subset_iff.mpr (by rw [← Finset.mem_singleton.mp (h (here_mem p))]; exact here_mem _)
lemma seed_le {p:Pod}{i:Slot}:seed i≤p ↔ i∈p.val:= Finset.singleton_subset_iff
lemma seed_of_one {p:Pod}(hp:p.card=1):p=seed p.here:=by
    have hx:= seed_le.mpr (here_mem p); exact (eq_of_le_of_not_lt hx (fun h=> by simpa [hp,card_seed,LT.lt.false] using (lt_card h))).symm
lemma card_one {p: Pod} : p.card=1 ↔ p=seed p.here:=⟨seed_of_one, fun h=> (congr_arg Pod.card h).trans (card_seed _)⟩
lemma disjoint_of_le {p q r s:Pod}(h:p≤q)(he:r≤s)(hp:Disjoint q.val s.val): Disjoint p.val r.val:= hp.mono h he
lemma not_disjoint (p:Pod):¬Disjoint p.val p.val:=fun h=> Finset.disjoint_left.mp h (here_mem p) (here_mem p)
lemma eq_of_here {p q:Pod}(h:∀ i∈p.val, i=q.here):p= seed q.here:=by apply le_seed; intro i hi; exact (Finset.mem_singleton.mpr (h i hi) : i ∈ ({q.here}:Finset _))
end Pod
attribute [local instance] Classical.propDecidable
structure Ensemble where
    choose : Finset Pod
    pairwise : (choose:Set Pod).PairwiseDisjoint Subtype.val
namespace Ensemble
instance : CoeSort Ensemble Type:= ⟨fun x=> x.choose⟩ -- P indices coe
instance (P:Ensemble): Fintype P:= inferInstanceAs (Fintype P.choose)
instance {P:Ensemble}: DecidableEq P:= Classical.decEq P
local notation "ℙ" => Ensemble
@[ext] lemma ext {P Q:ℙ}(he:P.choose=Q.choose): P=Q:=by cases P;cases Q;congr

def only (p:Pod):Ensemble:= ⟨{p}, by rw [Finset.coe_singleton]; exact (Set.pairwiseDisjoint_singleton ..)⟩
def empty:Ensemble:=⟨∅,by simp⟩
def Along (x:ℙ) : Finset ℕ:= x.choose.biUnion fun y=> y.val
lemma mem_along (P:Ensemble)(i:Slot): i∈ Along P ↔ ∃ x∈ P.choose,i∈x.val:= by unfold Along; rw [Finset.mem_biUnion]
lemma mem_coe {P:Ensemble} (p:P): (show Pod from p.val) ∈ P.choose:= p.property -- usage
lemma same {P: Ensemble}{p q:Pod}(h:p∈ P.choose)(he:q∈ P.choose){i:Slot}(hp:i∈p.val)(hq:i∈ q.val): p=q:= by_contra (fun hv=> Finset.disjoint_left.mp (P.pairwise h he hv) hp hq)
lemma serial (P:Ensemble){p q:P}{i:Slot}(hp:i∈ p.val.val)(hq:i∈ q.val.val): p=q:= Subtype.ext (same p.property q.property hp hq)

def owner (P:Ensemble) (i:P.Along): P:= ⟨((mem_along P _).mp i.property).choose, ((mem_along P _).mp i.property).choose_spec.1⟩
lemma belongs (P:Ensemble) (i:P.Along): i.val ∈ (owner P i).val.val:= ((mem_along P _).mp i.property).choose_spec.2
lemma only_mem {p q:Pod}:p∈(only q).choose ↔ p=q:=mem_singleton
instance {x:Pod}: Unique (only x) where
  default := ⟨x,mem_singleton_self _⟩
  uniq p := Subtype.ext (only_mem.mp p.property)
lemma only_def (x:Pod): (default:(only x)).val = x:=rfl
lemma along_only (x:Pod): Along (only x)=x.val:= by unfold Along only; simp
lemma choose_none {P:Ensemble}(hp:P.Along=∅): P=empty:=by
    refine ext (Finset.eq_empty_iff_forall_notMem.mpr (fun i hi=> ?_))
    have hh:= mem_along P i.here|>.mpr ⟨i,hi,i.here_mem⟩; simp [hp] at hh
lemma rank_split (P:Ensemble) : ∑ p:P, p.val.card = (Along P).card := by
   rw [Along, Finset.card_biUnion P.pairwise]; exact Finset.sum_coe_sort _ (Pod.card) -- inspect
end Ensemble
end YM.Frontier6.Bouquet
