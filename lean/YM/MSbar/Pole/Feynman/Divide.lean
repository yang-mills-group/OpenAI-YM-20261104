import YM.MSbar.Pole.Feynman.Graph

/-! Deletion of an edge, protecting all kinematic slots. -/
noncomputable section
set_option autoImplicit false
namespace YM.MSbar.Pole.Feynman.District
open Set Function Filter MeasureTheory Momentum Ambient Age Mellin place Symbol Sew Thread
open scoped Topology ContDiff BigOperators Classical
variable {I V:Type} {D:District I V} {C:Chart I V}

def within (S: Finset V)(e:I×I)(D:District I V)(C:Chart I V) : District I V:= ⟨S,(D.paths.erase e).filter fun p=> C.home p.1∈S⟩
-- helper for choosing cuts, oriented to first
structure Gap (S : Finset V) (e : I×I) (D : District I V) (C : Chart I V) : Prop where
  subset : S⊆D.lands
  yes : C.home e.1∈S
  no : C.home e.2∉S
  deep : ∀ p∈ D.paths.erase e, C.home p.1∈S ↔ C.home p.2∈S
namespace Clear
variable {S : Finset V} {e : I×I}
variable (h:D.Clear C) (he:e∈D.paths)
include h he
lemma pathV {p:I×I} (hp:p∈D.paths) : C.home p.1∈D.lands∧ C.home p.2∈D.lands:= by
  obtain ⟨-,hh,hg,_⟩:=h.boundary _ hp; exact ⟨(Finset.mem_filter.mp hh).2,(Finset.mem_filter.mp hg).2⟩
lemma splits (hp: ¬(D.less e).Crossing C) : ∃ S, Gap S e D C := by
  unfold Crossing at hp; push Not at hp; obtain ⟨S,hs,hg,h₁,h₂⟩:=hp
  change S⊆D.lands at hs; change ∀ p∈D.paths.erase e,_ at hg; change S≠D.lands at h₂
  have hh : ¬ (C.home e.1∈S ↔ C.home e.2∈S):=by
    intro hv; refine (or_iff_not_imp_left.mp (h.connected S hs fun p hp=>?_ ) h₁.ne_empty|> h₂)
    by_cases hq:p=e
    · subst p; exact hv
    exact hg p (Finset.mem_erase.mpr ⟨hq,hp⟩)
  obtain ⟨hL,hR⟩:=pathV h he he
  by_cases ht:C.home e.1∈S
  · exact ⟨S,hs,ht,fun hi=>hh (iff_of_true ht hi),hg⟩
  by_cases hm:C.home e.2∈S
  · refine ⟨D.lands \ S, Finset.sdiff_subset,Finset.mem_sdiff.mpr ⟨hL,ht⟩, (fun i=> (Finset.mem_sdiff.mp i).2 hm),fun x hx=>?_⟩
    obtain ⟨hf,hk⟩:=pathV h he (Finset.mem_of_mem_erase hx); simp only [Finset.mem_sdiff, hf,hk, true_and,hg x hx]
  exact False.elim (hh (iff_of_false ht hm))

-- every region containing exactly one of the new ends is connected
private lemma side (hs:S⊆D.lands) (p:I)(hp:p=e.1∨p=e.2)
    (hx:C.home p ∈ S) (hz:(p=e.1 ∧ C.home e.2∉S)∨ (p=e.2∧C.home e.1∉S))
    (hh:∀ q∈D.paths.erase e,C.home q.1∈S↔C.home q.2∈S): (within S e D C).Clear C := by
  have hb {q : I×I} (hm:q∈(within S e D C).paths): q∈D.paths ∧ C.home q.1∈S∧ C.home q.2∈S:= by
    obtain ⟨hl,hq⟩:=Finset.mem_filter.mp hm; exact ⟨Finset.mem_of_mem_erase hl,hq,(hh q hl).mp hq⟩
  constructor
  · have hr (W:Finset V)(hw:W⊆ S) (hm:C.home p∉ W) (hg:∀ q∈(within S e D C).paths,C.home q.1∈ W ↔ C.home q.2∈W): W=∅:=by
      refine (h.connected W (hw.trans hs) (fun q hq=>?_)).resolve_right (fun heq=>hm (heq.symm ▸ hs hx))
      by_cases ha:q=e
      · subst q
        rcases hz with ⟨hz,hl⟩|⟨hz,hl⟩ <;> subst p
        · exact iff_of_false hm fun ht=>hl (hw ht)
        exact iff_of_false (fun ht=>hl (hw ht)) hm
      have hv := Finset.mem_erase.mpr ⟨ha,hq⟩
      by_cases hb : C.home q.1 ∈ S
      · exact hg q (Finset.mem_filter.mpr ⟨hv,hb⟩)
      exact iff_of_false (fun ha=> hb (hw ha)) fun hk=> hb ((hh q hv).mpr (hw hk))
    intro W hW H; by_cases ha:C.home p∈ W
    · have hv : S\W=∅ := by
        refine hr _ Finset.sdiff_subset (fun ht=> (Finset.mem_sdiff.mp ht).2 ha) (fun p hp=>?_)
        obtain ⟨-,hb,hk⟩:=hb hp; simp only [Finset.mem_sdiff,hb,hk,true_and,H p hp]
      exact Or.inr (Finset.Subset.antisymm hW (Finset.sdiff_eq_empty_iff_subset.mp hv))
    left; exact hr W hW ha H
  · have ho: p∈ (within S e D C).mouths C:= by
      refine Finset.mem_sdiff.mpr ⟨?_,?_⟩
      · apply Finset.mem_filter.mpr; refine ⟨?_,hx⟩; rcases hp with hL|hL <;> subst p
        · exact (Finset.mem_filter.mp (h.boundary e he).2.1).1
        exact (Finset.mem_filter.mp (h.boundary e he).2.2.1).1
      intro hm; obtain ⟨q,hq,hp'⟩:= Finset.mem_biUnion.mp hm
      have ht : p∈ ends (D.paths.erase e):= Finset.mem_biUnion.mpr ⟨q,(Finset.mem_filter.mp hq).1,hp'⟩
      rcases hp with hL|hL <;> subst p
      · exact (h.excludes he).1 ht
      exact (h.excludes he).2 ht
    exact ⟨p,ho⟩
  · intro p hp; obtain ⟨hv,hx,hp⟩:=hb hp; obtain ⟨ha,hb,hk,ht⟩:=h.boundary p hv
    exact ⟨ha,Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hb).1,hx⟩, Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hk).1,hp⟩,ht⟩
  exact fun p q hp hq hg=> h.unique p q (hb hp).1 (hb hq).1 hg
variable (g:Gap S e D C)
include g
local notation "T" => D.lands \ S
private lemma same p (hp:p∈D.paths.erase e) : C.home p.1∈T ↔ C.home p.2∈T:= by
  obtain ⟨hl,ht⟩:=pathV h he (Finset.mem_of_mem_erase hp); simp only [Finset.mem_sdiff,hl,ht,true_and,g.deep p hp]
lemma content : (within S e D C).Clear C ∧ (within T e D C).Clear C:=
  ⟨side h he g.subset e.1 (Or.inl rfl) g.yes (Or.inl ⟨rfl,g.no⟩) g.deep,
   side h he Finset.sdiff_subset e.2 (Or.inr rfl) (Finset.mem_sdiff.mpr ⟨(pathV h he he).2,g.no⟩) (Or.inr ⟨rfl,fun h=> (Finset.mem_sdiff.mp h).2 g.yes⟩) (same h he g)⟩

omit g in
private lemma regional (hs:S⊆D.lands) (hh:∀ q∈D.paths.erase e,C.home q.1∈S↔C.home q.2∈S) :
    (within S e D C).mouths C=((D.less e).mouths C).filter fun i=> C.home i∈S := by
  ext x; rw [Finset.mem_filter]
  have ht (hS:C.home x∈S): x∈ends ((within S e D C).paths) ↔ x∈ ends (D.paths.erase e) := by
    simp only [ends,Finset.mem_biUnion]; constructor
    · rintro ⟨q,hk,hp⟩; exact ⟨q,(Finset.mem_filter.mp hk).1,hp⟩
    rintro ⟨q,hk,hp⟩; refine ⟨q,Finset.mem_filter.mpr ⟨hk,?_⟩,hp⟩
    simp only [Finset.mem_insert,Finset.mem_singleton] at hp
    rcases hp with hp|hp
    · simpa only [← hp]
    exact (hh q hk).mpr (hp ▸ hS)
  change x∈ C.venues S \ _ ↔ x ∈ (C.venues D.lands) \ ends (D.paths.erase e) ∧ _; simp only [Finset.mem_sdiff,C.appears];
  by_cases hz:C.home x∈S
  · rw [ht hz]; simp [hz,hs hz]
  simp [hz,within]
lemma mouth_regions : (within S e D C).mouths C=((D.less e).mouths C).filter (fun i=> C.home i ∈ S) ∧
    (within T e D C).mouths C=((D.less e).mouths C).filter (fun i=> C.home i∈T):=
  ⟨regional h he g.subset g.deep,regional h he Finset.sdiff_subset (same h he g)⟩
lemma split_union : (within S e D C).mouths C∪(within T e D C).mouths C=(D.less e).mouths C:=by
  obtain ⟨hs,hp⟩:= mouth_regions h he g; rw [hs,hp]; ext i; simp only [Finset.mem_union,Finset.mem_filter,← and_or_left,Finset.mem_sdiff]
  constructor
  · exact And.left
  intro hv; have he:= (Finset.mem_filter.mp (Finset.mem_sdiff.mp hv).1).2
  refine ⟨hv,?_⟩; tauto
lemma split_disjoint : Disjoint ((within S e D C).mouths C) ((within T e D C).mouths C):= by
  obtain ⟨hs,hp⟩:= mouth_regions h he g; rw [hs,hp]; exact Finset.disjoint_left.mpr fun i hv hw => (Finset.mem_sdiff.mp (Finset.mem_filter.mp hw).2).2 (Finset.mem_filter.mp hv).2
end Clear
end YM.MSbar.Pole.Feynman.District
