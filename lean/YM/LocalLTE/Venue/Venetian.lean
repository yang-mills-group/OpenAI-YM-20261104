import YM.LocalLTE.Venue.Palm
/-! # Following reallocations with live soft terms. -/
set_option autoImplicit false
noncomputable section
namespace YM.Merge.Motion
open Function Filter Set Lattice Wilson RG Ovens Ovens.Pipes MeasureTheory Work.H03
open Pressure Progress.DirectedRecipe Rack ConnectedActivityE6 Finset Push Push.AbsoluteSums
open PhysicalNext.Repeat Mallow Daisy Switch
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {ι:Type}[Fintype ι] {G : Gauge}{n : Side}
    {X:Pipes G n} {d:Tap G n} {P : BudgetPoint} {r c δ A B κ γ w v a:ℝ} {o : Site n}
set_option quotPrecheck false
variable (P) (F:ℕ≃ Pellet X)(ha:HasSlots P (X.pours d))
local notation "L₀"=>singleLeft X
local notation "L₁"=>sleepK G n
def liable (j:ℕ) : Prop:= ∃ i:ℕ,i∉ Set.range (sleepK G n)∧ singleLeft X i=F j
-- put singles outside L at same address. all else L with their own second parameter. deterministic & recoverable.
def lands (j:ℕ) :ℕ:= if h: liable F j then Classical.choose h else L₁ (readFoot (addr F P j),j)
lemma landing (j)(h:liable F j): lands P F j∉ Set.range L₁∧ L₀ (lands P F j)=F j:=by
    unfold lands; rw [dif_pos h]; exact Classical.choose_spec h
lemma lay (j)(h:¬liable F j): lands P F j= L₁ (readFoot (addr F P j),j):=dif_neg h
def arrange : ℕ ↪ ℕ where
   toFun:= lands P F
   inj':= fun i j h=>by
    by_cases he:liable F i
    · have hv:liable F j:= by by_contra hz; exact (landing P F _ he).1 ⟨_, ((lay P F _ hz).symm.trans h.symm)⟩
      exact F.injective ((landing P F _ he).2.symm.trans ((congr_arg L₀ h).trans (landing P F _ hv).2))
    by_cases hv:liable F j; · exact False.elim ((landing P F _ hv).1 ⟨_, (lay P F _ he).symm.trans h⟩)
    exact congr_arg Prod.snd ((L₁).injective ((lay P F _ he).symm.trans (h.trans (lay P F _ hv))))
lemma lite (j)(i) (h:F j=singleLeft X i) : readFoot (addr F P j)=readFoot (X.kernel i):=by
    refine foot_ext ?_ ?_
    · change X.skin (F j).val=_; rw [h]; change Finset.biUnion {Sum.inl i} _= _; rw [Finset.singleton_biUnion]; rfl
    change X.plot (F j).val=_; rw [h]; change Finset.biUnion (lefts {Sum.inl i}) _ = _
    have ht:lefts {Sum.inl i}={i}:=by ext; simp [lefts]
    rw [ht,Finset.singleton_biUnion];rfl
lemma summer (j i) (h:F j = singleLeft X i)(U:Config G n): (addr F P j).eligible P.threshold U ↔ (X.kernel i).eligible P.threshold U:=by
    have ht:= lite P F j i h; constructor
    · intro he; exact he.2 i (show i∈lefts (F j).val from by rw [h]; exact mem_toLeft.mpr (Finset.mem_singleton_self _))
    intro ht'
    refine ⟨?_,?_⟩
    · rw [show (addr F P j).support= _ from (show (addr F P j).support=(X.kernel i).support from congr_arg Foot.support ht), show (addr F P j).inventory=(X.kernel i).inventory from congr_arg Foot.inventory ht]; exact ht'.1
    intro j hj; rw [h] at hj; have he' : j=i:= Sum.inl.inj (Finset.mem_singleton.mp (Finset.mem_toLeft.mp (show j∈lefts (L₀ i).val from hj))); rwa [he'] -- rcases error
lemma leaves (j)(i) (h:F j = singleLeft X i) (hx:(X.pours d).ForcedFamily P) : solid F P (alt (d:=d) d.forced 0) j=d.forced i:=by
    funext U; unfold solid; split
    next hh=> rw [h]; change Finset.prod {Sum.inl i} _= _; rw [Finset.prod_singleton]; rfl
    next hh=> exact Eq.symm (Classical.byContradiction (fun h'=>hh ((summer P F j i h _).2 (hx.permit i U h'))))
-- hard-only pellet one.R.
lemma jewel (t:X.Pellet)(h: ¬∃ j:ℕ,Sum.inr j∈ t.val): ∃ i,t= singleLeft X i:=by
    obtain ⟨j,hj⟩:=t.property.1
    have hj':Sum.inl j∈t.val:= Finset.mem_toLeft.mp hj
    have he (i j)(hh:Ac.bonds X.patch t.val i j) : i=j := by
        rcases i with i|i; swap; · exact False.elim (h ⟨i,hh.1⟩)
        rcases j with j|j; swap; · exact False.elim (h ⟨j,hh.2.1⟩)
        by_contra hz; obtain ⟨x,hX,hz'⟩:= hh.2.2
        have hv:= t.property.2.2 (Finset.mem_toLeft.mpr hh.1) (Finset.mem_toLeft.mpr hh.2.1) (fun h=>hz (congr_arg _ h)); exact Finset.disjoint_left.mp hv hX hz'
    have hp b (hx:Ac.chain X.patch t.val (Sum.inl j) b) : Sum.inl j=b:=by induction hx with| refl=>rfl| tail _ h ih=>exact ih.trans (he _ _ h)
    refine ⟨j,Subtype.ext (Finset.Subset.antisymm ?_ (Finset.singleton_subset_iff.mpr hj'))⟩
    intro z hz; exact Finset.mem_singleton.mpr (hp z (t.property.2.1.2 _ hj' z hz)).symm
lemma charL (j)(h:F j∉Set.range (singleLeft X)):solid F P (alt (d:=d) d.forced 0) j=0:=by
    have he: ∃ i:ℕ,Sum.inr i∈ (F j).val:= by by_contra hz; obtain ⟨i,hp⟩:= jewel (F j) hz; exact h ⟨i,hp.symm⟩ -- P not argument?
    obtain ⟨i,hp⟩:= he
    funext U; unfold solid; split
    · refine Finset.prod_eq_zero hp ?_
      change Real.exp ((0:ℝ))-1=0; rw [Real.exp_zero,sub_self]
    rfl
local notation "F₀"=> arrange P F
local notation "g"=> alt (d:=d) d.forced 0
include ha
lemma locale (j) : readFoot (X.kernel (arrange P F j))=readFoot (addr F P j):=by
    have hw:X.kernel=addr (folio G n) P:=ha.forced
    by_cases h:liable F j
    · exact (lite P F j _ (landing P F _ h).2.symm).symm
    calc readFoot (X.kernel _)=readFoot (X.kernel (L₁ (readFoot (addr F P j),j))):= congr_arg (readFoot ∘ X.kernel) (lay P F _ h)
         _=_:= by rw [hw]; apply tile_exact
lemma carriesG (j)(U)(h:(addr F P j).eligible P.threshold U): (X.kernel (arrange P F j)).eligible P.threshold U:=by
    have ht:=locale P F ha j; by_cases he:liable F j;
    · exact (summer P F j _ (landing P F _ he).2.symm U).1 h
    have hw : X.kernel (arrange P F j) = addr (folio G n) P (L₁ (readFoot (addr F P j),j)):=by rw [show X.kernel=addr (folio G n) P from ha.forced,show arrange P F j= _ from lay P F j he]
    refine ⟨?_, hw.symm ▸ ?_⟩
    · exact (congr_arg (·∩RG.flags P.threshold U) (congr_arg Foot.support ht)).trans (h.1.trans (congr_arg Foot.inventory ht).symm)
    exact (tile_test P _ _ U).2 h.1 -- edit args
lemma once (hx:(X.pours d).ForcedFamily P) (j:ℕ): solid F P (g) j=d.forced ((F₀) j):=by
    by_cases h:liable F j; · exact leaves P F j _ (landing P F _ h).2.symm hx
    rw [show F₀ j=_ from (lay P F j h),show d.forced (L₁ (readFoot (addr F P j),j))=0 from ha.forced_zero (readFoot (addr F P j),j)]
    by_cases he:F j∈ Set.range L₀; swap; · exact charL P F j he
    obtain ⟨i,hi⟩:=he; rw [leaves P F j _ hi.symm hx]; obtain ⟨z,hz⟩: i∈Set.range L₁:=Classical.byContradiction (fun hn=> h ⟨i,hn,hi⟩); rw [← hz];exact ha.forced_zero z
lemma unusedG (j:ℕ) (h:j∉ Set.range (arrange P F)):d.forced j=0:=by
    by_cases he : j∈ Set.range L₁
    · obtain ⟨z,rfl⟩:=he; exact ha.forced_zero z
    obtain ⟨i,hi⟩:= F.surjective (singleLeft X j); exact False.elim (h ⟨i,(singleLeft X).injective ((landing P F i ⟨j,he,hi.symm⟩).2.trans hi)⟩)
lemma adjusts (l k:Code G n): Readdress P (Function.Embedding.refl _) (arrange P F) (fused F P (alt (d:=d) k l)) (black (X.pours d) (stuff F₀ (solid F P (alt (d:=d) k l)))):=by
    exact ⟨fun _=>rfl,fun i=>congr_arg Foot.support (locale P F ha i),fun i=>congr_arg Foot.inventory (locale P F ha i),fun i=>rfl,fun i=> stuffed ..,fun i hi=>False.elim (hi ⟨i,rfl⟩),fun i hi=> blank _ _ hi,carriesG P F ha⟩
end YM.Merge.Motion
