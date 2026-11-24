import YM.RG02.Wick.Overlay
import YM.RG02.Wick.Tags

/-!
Joint tag/line cumulants. Need BOTH sorts of connections.
Cancellation is per full pairing before any absolute sum, among all
partitions allowing its lines. No drawing from an IID law required except
in the `Multiplying` on the actual dependencies in an asserted disjoint cut.
Complete supports of factors, or telescope balls for both vertex and line
decompositions, plug in here. No assertion that an interacting term is bound
by the corresponding *single* graph cost ignoring partition-sum costs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG02.Wick
open Filter Marker Multi Finset Extra.Trajectories Marks Next.Rank Next.Rank.Normal Actor
open scoped BigOperators Classical
variable {A V I : Type} [DecidableEq A] [Fintype A] [DecidableEq V] {R : Census V}

/-- Vertices own uniquely numbered physical legs, but two leg reads may
see exactly the SAME random variable. -/
def paidFor (o : A→V)(p : Multi.Hot (full A)) := p.val.val.image o

/-- Hand all tag-dependency radii for lines to their incident vertices. -/
def budget [DecidableEq I] (s : V→Finset I) (w : Multi.Hot (full A)→Finset I)
    (o : A→V)(t : (Lines A).Mode) (i : V) :=
  s i ∪ (t.val.filter (fun j => i∈paidFor o j)).biUnion w

def graph [DecidableEq I] (s : V→Finset I) (w : Multi.Hot (full A)→Finset I)
    (o : A→V)(t : (Lines A).Mode) (i j : V) : Prop :=
   (∃ b∈t.val, i∈paidFor o b ∧ j∈paidFor o b) ∨ ¬ Disjoint (budget s w o t i) (budget s w o t j)

section weight
variable {T W : Type} {μ : (T → ℂ)→ₗ[ℂ]ℂ}

def terms (o : A→V)(c : V → T → ℂ)(h : Multi.Hot (full A) → T → ℂ)(μ : (T → ℂ)→ₗ[ℂ]ℂ) : Poly (together R (Lines A)) :=
  Poly.inject fun s => if Paired o s then
      μ ((∏ i∈(Pair.fst s).val,c i) * ∏ p∈(Pair.snd s).val,h p) else 0

lemma terms_paired (o : A → V)(c : V → T → ℂ)(h : Multi.Hot (full A) → T → ℂ) :
    Retains o (terms (R:=R) o c h μ) := fun _ hn => if_neg hn
lemma terms_quiet (o : A → V)(c : V → T → ℂ)(h : Multi.Hot (full A) → T → ℂ)(hμ : μ 1=1) :
    (terms o c h μ).part (together R (Lines A)).quiet=1 := by
   change (if Paired o (together R (Lines A)).quiet then _ else _)=1
   rw [if_pos (paired_quiet _)]
   simp only [Pair.fst_quiet,Pair.snd_quiet]
   change μ ((∏ i∈∅, c i)* ∏ i∈∅,h i)=1
   simpa using hμ

def edges (q : T → Symmetric W)(ℓ : T → A → W)(b : Multi.Hot (full A)) (u : T) := two (q u) (ℓ u) b.val
/-- Complete moment on any given mode. -/
def monomials (o : A→V)(c : V → T → ℂ)(q : T → Symmetric W)(ℓ : T → A → W)(μ : (T → ℂ)→ₗ[ℂ]ℂ) : Poly R :=
  Poly.inject fun s => μ fun u => (∏ i∈s.val,c i u) * blend (q u) 0 (glyphs (ℓ u) (arms o s.val))

theorem joint_assembly (o : A→V)(c : V → T → ℂ)(q : T → Symmetric W)(ℓ : T → A → W)(μ : (T → ℂ)→ₗ[ℂ]ℂ) :
   monomials (R:=R) o c q ℓ μ=compress R A (terms o c (edges q ℓ) μ) := by
  ext s
  let F (p : (Lines A).Mode) : T → ℂ := if CompleteOn (arms o s.val) p then (∏ i∈s.val,c i) * ∏ i∈p.val,edges q ℓ i else 0
  have ht p : (terms (R:=R) o c (edges q ℓ) μ).part (Pair.mk s p)=μ (F p) := by
    change (if _ then _ else _)=_
    unfold F
    by_cases h : Paired o (Pair.mk s p)
    · rw [if_pos h,if_pos (show CompleteOn (arms o s.val) p from by simpa only [Paired,Pair.fst_mk,Pair.snd_mk] using h),Pair.fst_mk,Pair.snd_mk]
    rw [if_neg h, if_neg (show ¬ CompleteOn (arms o s.val) p from by simpa only [Paired,Pair.fst_mk,Pair.snd_mk] using h),map_zero]
  have he (t : T) : (∑ i : (Lines A).Mode,F i) t = (∏ i∈s.val, c i t) * blend (q t) 0 (glyphs (ℓ t) (arms o s.val)) := by
    rw [pairing, mul_sum,Finset.sum_apply]
    apply sum_congr rfl; intro i hi
    dsimp only [F]
    split
    · simp only [Pi.mul_apply,Finset.prod_apply]; rfl
    simp
  rw [compress_part]; simp_rw [ht]; rw [← map_sum];
  change μ _ = μ _
  · exact congr_arg _ (funext he).symm

-- never use tag-by-tag log here: independent normalization required after μ.
lemma monomial_graph_sum [Fintype V] (o : A → V)(c : V → T → ℂ)(q : T → Symmetric W)(ℓ : T → A → W)(H : μ 1=1) (s : R.Mode) :
    (connected (monomials o c q ℓ μ)).part s=∑ p : (Lines A).Mode,(connected (terms o c (edges q ℓ) μ)).part (Pair.mk s p) := by
  rw [joint_assembly, ← (terms_paired o c (edges q ℓ)).relates (terms_quiet o c _ H),compress_part]

end weight

section vanish
variable (o : A → V)(p : (Lines A).Mode) (X : Finset V)

private def runs := p.val.filter (fun b => paidFor o b ⊆ X)

private lemma boundary (a : R.Mode)(b : (Lines A).Mode)(x : Finset V) (y : Finset (Multi.Hot (full A))) :
    Marks.inside (x.disjSum y) (Pair.mk a b) = Pair.mk (Marks.inside x a) (Marks.inside y b) ∧
      Marks.outside (x.disjSum y) (Pair.mk a b)=Pair.mk (Marks.outside x a) (Marks.outside y b) := by
   constructor
   · apply Subtype.ext; unfold inside Pair.mk; ext i; cases i <;> simp
   apply Subtype.ext; unfold outside Pair.mk; ext i; cases i <;> simp

private lemma splitting {Q : Type} [DecidableEq Q] (B : Census Q)(v : B.Mode)(y : Finset Q) :
    Poly.merges (Marks.inside y v) (Marks.outside y v) v := by
   unfold Poly.merges inside outside; refine ⟨?_,?_⟩
   · exact Finset.disjoint_left.mpr fun i hi hv => (mem_sdiff.mp hv).2 (mem_inter.mp hi).2
   ext a; simp only [mem_inter, Finset.mem_sdiff,mem_union]; tauto

-- No pair meets both sides of cut
private lemma still {o : A→V}{X : Finset V}{p : (Lines A).Mode}
    {z : (Lines A).Mode}{f : R.Mode}(hp : z.val⊆p.val)
    (he : ∀ i∈p.val, (paidFor o i)⊆X ∨ Disjoint (paidFor o i) X) :
    Paired o (Pair.mk f z) ↔
      Paired o (Pair.mk (Marks.inside X f) (Marks.inside (runs o p X) z)) ∧
        Paired o (Pair.mk (Marks.outside X f) (Marks.outside (runs o p X) z)) := by
  let U := runs o p X
  constructor
  · intro h
    unfold Paired at *
    simp only [Pair.fst_mk,Pair.snd_mk] at *
    have ht (i : A) : (∃ b∈z.val, i∈b.sites) ↔ o i∈f.val := by rw [← arm_of, ← h.1]; exact mem_biUnion.symm
    have hm (i : A)(b : Multi.Hot (full A))(hb : b∈z.val)(hi : i∈ b.sites) : b∈U ↔ o i∈ X := by
       unfold U runs; constructor
       · intro hn; exact (mem_filter.mp hn).2 (mem_image_of_mem _ hi)
       intro hn; exact mem_filter.mpr ⟨hp hb,(he _ (hp hb)).resolve_right fun h => Finset.disjoint_left.mp h (mem_image_of_mem _ hi) hn⟩
    constructor
    · constructor
      · ext i
        change i∈ (z.val ∩ U).biUnion Multi.Hot.sites ↔ _
        rw [arm_of]; constructor
        · intro h; obtain ⟨b,H,Hb⟩ := mem_biUnion.mp h; obtain ⟨ha,hC⟩ := mem_inter.mp H
          exact mem_inter.mpr ⟨(ht i).mp ⟨b,ha,Hb⟩,(hm i b ha Hb).mp hC⟩
        intro h; obtain ⟨ha,hC⟩ := mem_inter.mp h; obtain ⟨b,H,Hb⟩ := (ht i).mpr ha
        exact mem_biUnion.mpr ⟨b,mem_inter.mpr ⟨H,(hm i b H Hb).mpr hC⟩,Hb⟩
      exact fun i hi => h.2 i (mem_inter.mp hi).1
    constructor
    · ext i
      change i∈(z.val \ U).biUnion Multi.Hot.sites ↔ _
      rw [arm_of]; constructor
      · intro H; obtain ⟨b,H,Hb⟩ := mem_biUnion.mp H; obtain ⟨ha,hC⟩ := mem_sdiff.mp H
        exact mem_sdiff.mpr ⟨(ht i).mp ⟨b,ha,Hb⟩,fun k => hC ((hm i b ha Hb).mpr k)⟩
      intro h; obtain ⟨ha,hC⟩ := mem_sdiff.mp h; obtain ⟨b,H,Hb⟩ := (ht i).mpr ha
      exact mem_biUnion.mpr ⟨b,mem_sdiff.mpr ⟨H,fun k => hC ((hm i b H Hb).mp k)⟩,Hb⟩
    exact fun i hi => h.2 i (mem_sdiff.mp hi).1
  rintro ⟨h,h'⟩; exact paired_join h h' ((Pair.merges ..).mpr ⟨splitting ..,splitting ..⟩)

private lemma depends [DecidableEq I] {D : I → Type}{X : Finset V}
    {p : (Lines A).Mode}{s : (together R (Lines A)).Mode}{o : A→V}(hp : Paired o s)
    {f : V → Draw D → ℂ}{g : Multi.Hot (full A) → Draw D → ℂ}
    {c : V → Finset I}{w : Multi.Hot (full A) → Finset I}(hs : ∀ i,Needs (f i) (c i))(ht : ∀ i,Needs (g i) (w i))
    (hv : (Pair.snd s).val⊆p.val)(hl : (Pair.fst s).val ⊆ X) :
    Needs ((∏ i∈(Pair.fst s).val,f i) * ∏ i∈(Pair.snd s).val,g i) (X.biUnion (budget c w o p)) := by
   apply Needs.mul
   · exact Needs.product fun i hi => (hs i).enlarge fun _ hh => mem_biUnion.mpr ⟨i,hl hi, Finset.mem_union_left _ hh⟩
   apply Needs.product; intro i hi
   obtain ⟨j,hj⟩ := i.property
   apply (ht i).enlarge; intro x hx
   refine Finset.mem_biUnion.mpr ⟨o j,hl ?_,Finset.mem_union_right _ (Finset.mem_biUnion.mpr ?_)⟩
   · exact arm_of.mp (hp.1 ▸ Finset.mem_biUnion.mpr ⟨i,hi,hj⟩)
   exact ⟨i,mem_filter.mpr ⟨hv hi, mem_image_of_mem _ hj⟩,hx⟩

-- no overlap yields factorization of the complete moment stats for THIS pairing, all subprofiles, including zeros
private theorem splits_at [DecidableEq I] {D : I → Type}{x : R.Mode}
    {p : (Lines A).Mode}{o : A→V}{μ : (Draw D→ℂ)→ₗ[ℂ]ℂ} (Hμ : Multiplying μ) (hp : Paired o (Pair.mk x p))
    {f : V → Draw D → ℂ}{g : Multi.Hot (full A) → Draw D → ℂ}
    {c : V → Finset I}{w : Multi.Hot (full A) → Finset I}(hs : ∀ i,Needs (f i) (c i))(ht : ∀ i,Needs (g i) (w i))
    {X : Finset V}(_hX : X⊆ x.val)(he : ∀ i∈X, ∀ j∈x.val \ X, ¬ graph c w o p i j) :
    Divides (terms (R:=R) o f g μ) (X.disjSum (runs o p X)) (Pair.mk x p).val := by
   let M : Poly (together R (Lines A)) := terms o f g μ
   have hk (b) (hb:b∈p.val) : paidFor o b ⊆ x.val := by
      unfold Paired at hp; simp only [Pair.snd_mk,Pair.fst_mk] at hp
      intro i hi; obtain ⟨a,ha,rfl⟩ := mem_image.mp hi
      exact arm_of.mp (hp.1 ▸ mem_biUnion.mpr ⟨b,hb,ha⟩)
   have hl (b) (hb : b∈p.val) : (paidFor o b)⊆X ∨ Disjoint (paidFor o b) X := by
      by_cases h : paidFor o b ⊆ X; exact Or.inl h
      right; obtain ⟨j,hj,he'⟩ := not_subset.mp h
      exact Finset.disjoint_left.mpr (fun i hi hI => he i hI j (mem_sdiff.mpr ⟨hk _ hb hj,he'⟩) (Or.inl ⟨b,hb,hi,hj⟩))
   have hd : Disjoint (X.biUnion (budget c w o p)) ((x.val \ X).biUnion (budget c w o p)) := by
      apply disjoint_left.mpr; intro i hi hh
      obtain ⟨a,ha,hA⟩ := mem_biUnion.mp hi; obtain ⟨b,hb,hB⟩ := mem_biUnion.mp hh
      exact he _ ha _ hb (Or.inr fun HG => Finset.disjoint_left.mp HG hA hB)
   intro t HA
   obtain ⟨⟨a,b⟩,rfl⟩ := Pair.iso.surjective t
   let Y := runs o p X
   change (Pair.mk a b).val ⊆ _ at HA
   have hx : a.val⊆x.val := fun i hi => Finset.inl_mem_disjSum.mp (HA (Finset.inl_mem_disjSum.mpr hi))
   have hv : b.val⊆p.val := fun i hi => Finset.inr_mem_disjSum.mp (HA (Finset.inr_mem_disjSum.mpr hi))
   let L := Pair.mk (Marks.inside X a) (Marks.inside Y b)
   let P := Pair.mk (Marks.outside X a) (Marks.outside Y b)
   obtain ⟨hb,Hb⟩ := boundary a b X Y
   change M.part (Pair.mk a b) = M.part (Marks.inside (X.disjSum Y) (Pair.mk a b)) * M.part (Marks.outside (X.disjSum Y) (Pair.mk a b)); rw [hb,Hb];
   let F (s : (together R (Lines A)).Mode) := (∏ i∈(Pair.fst s).val,f i) * ∏ j∈(Pair.snd s).val,g j
   change (if Paired o (Pair.mk a b) then μ (F (Pair.mk a b)) else 0) = (if Paired o L then μ (F L) else 0)*(if Paired o P then μ (F P) else 0)
   by_cases hh : Paired o (Pair.mk a b); swap
   · rw [if_neg hh]
     by_cases h : Paired o L
     · rw [if_neg (c:=Paired o P) (fun H => hh ((still hv hl).mpr ⟨h,H⟩)),mul_zero]
     rw [if_neg h,zero_mul]
   obtain ⟨hL,hP⟩ := (still hv hl).mp hh
   rw [if_pos hh,if_pos (show Paired o L from hL), if_pos (show Paired o P from hP)]
   have h1 : Needs (F L) _ := depends (show Paired o L from hL) hs ht (show (Pair.snd L).val ⊆ p.val from by rw [show Pair.snd L=_ from Pair.snd_mk ..]; exact (Finset.inter_subset_left).trans hv) (show _ ⊆ X from by rw [show Pair.fst L=_ from Pair.fst_mk ..]; exact inter_subset_right)
   have h2 : Needs (F P) _ := depends (show Paired o P from hP) hs ht (show (Pair.snd P).val ⊆ p.val from by rw [show Pair.snd P=_ from Pair.snd_mk ..]; exact Finset.sdiff_subset.trans hv) (show _ ⊆ x.val \ X from by rw [show Pair.fst P=_ from Pair.fst_mk ..]; exact Finset.sdiff_subset_sdiff_left X hx)
   rw [← Hμ.2 _ _ hd (F L) (F P) h1 h2]; congr 1
   have hg : F (Pair.mk a b)=F L*F P := by
      unfold F L P; simp only [Pair.fst_mk,Pair.snd_mk]
      have hu := splitting R a X; have hr := splitting (Lines A) b Y
      rw (occs:=.pos [1]) [← hu.2,prod_union hu.1]
      rw (occs:=.pos [1]) [← hr.2,prod_union hr.1]; ac_rfl
   exact hg

/-- Pair choices lacking connection vanish already separately. -/
theorem only_jointly [Fintype V][DecidableEq I]{D : I → Type}
    {μ : (Draw D→ℂ)→ₗ[ℂ]ℂ} (Hμ : Multiplying μ)
    {f : V → Draw D → ℂ}{g : Multi.Hot (full A) → Draw D → ℂ}
    {c : V → Finset I}{w : Multi.Hot (full A) → Finset I}(hs : ∀ i,Needs (f i) (c i))(ht : ∀ i,Needs (g i) (w i))
    (x : R.Mode) (h : (connected (terms o f g μ)).part (Pair.mk x p) ≠ 0) :
    Paired o (Pair.mk x p) ∧ NoCut x.val (graph c w o p) := by
   have he := terms_quiet (R:=R) o f g Hμ.1
   have hp : Paired o (Pair.mk x p) := by by_contra hn; exact h ((terms_paired o f g|>.logged he) _ hn)
   refine ⟨hp,fun X hx hX H => ?_⟩; by_contra! hn
   apply h; apply Marks.connected_vanish he _ _ _ (splits_at Hμ hp hs ht hx hn)
   · obtain ⟨i,hi⟩ := hX; exact ⟨Sum.inl i,mem_inter.mpr ⟨inl_mem_disjSum.mpr hi,inl_mem_disjSum.mpr (hx hi)⟩⟩
   obtain ⟨i,hi⟩ := H; obtain ⟨h1,h2⟩ := mem_sdiff.mp hi; exact ⟨Sum.inl i, mem_sdiff.mpr ⟨inl_mem_disjSum.mpr h1,h2 ∘ inl_mem_disjSum.mp⟩⟩

end vanish
end YM.RG02.Wick
