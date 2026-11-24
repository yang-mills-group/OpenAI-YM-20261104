import YM.Frontier6.Bouquet.Gate.Grab

/-! Cartesian bijection of refinements when already in disjoint groups. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet.Ensemble
open Function Set Finset
open scoped Topology BigOperators Classical
variable {P Q R: Ensemble}(h:Free P Q)
-- can take restriction by ancestry
private def portion (P Q:Ensemble) : Ensemble:= ⟨Q.choose.filter (fun i=>i∈P.enclosed), fun i hi j hj he=> Q.pairwise (Finset.mem_of_mem_filter _ hi) (Finset.mem_of_mem_filter _ hj) he⟩ -- name private
section
variable (H:R ≤ merge h)
-- decide left-right
include H
private lemma portionL : portion P R ≤ P:=by
    constructor
    · ext1 i; simp only [mem_along]; constructor
      · rintro ⟨p,hp,hi⟩; obtain ⟨q,hq,k⟩:=encloses.mp (mem_filter.mp hp).2; exact ⟨q,hq,k hi⟩
      rintro ⟨p,hp,hi⟩; obtain ⟨q,hq,hh⟩:= (mem_along ..).mp ((ref_slots H) ▸ (listed _ _ (germL h ⟨p,hp⟩).property hi))
      refine ⟨q, mem_filter.mpr ⟨hq, encloses.mpr ⟨p,hp, ?_⟩⟩,hh⟩; exact not_cross H hq (germL h ⟨p,hp⟩).property hh hi
    intro p hp; exact encloses.mp (mem_filter.mp hp).2
private lemma portionR : portion Q R ≤ Q:= portionL h.symm ((show merge h=merge h.symm from Ensemble.ext (Finset.union_comm ..)) ▸ H) -- include H
private lemma pair_halves : merge (h.refines (portionL h H) (portionR h H))= R:=by
    refine ext (Finset.ext fun p=>?_); rw [show p∈ (merge _).choose ↔ p∈ (portion P R).choose ∨ p∈ (portion Q R).choose from Finset.mem_union]; unfold portion; simp only [mem_filter,and_self_left]; constructor; exact fun h=> h.elim And.left And.left -- check
    intro hp; have hh:= under H (stage_in hp); rw [merge_enclosure] at hh; exact (Finset.mem_union.mp hh).elim (fun h=>Or.inl ⟨hp,h⟩) (fun h=> Or.inr ⟨hp,h⟩)
end

variable (X:Down P× Down Q)
def twine : Down (merge h):= ⟨merge (h.refines X.1.property X.2.property), merge_le h X.1.property X.2.property⟩
lemma twins : (twine h X).val.choose=X.1.val.choose ∪ X.2.val.choose:=rfl
lemma twine_unique : ∀ y:Down (merge h),∃! x, twine h x=y:=by
    intro ⟨R,H⟩; let a : Down P:=⟨portion P R, portionL h H⟩; let b :Down Q:=⟨portion Q R, portionR h H⟩; have he:twine h (a,b)=⟨_,H⟩:=Subtype.ext (pair_halves h H); refine ⟨(a,b),he,?_⟩
    rintro ⟨x,y⟩ hp
    have h1 (p:Pod) : p∈ R.choose ↔ p∈ x.val.choose ∨ p∈y.val.choose:= Eq.to_iff (congr_arg (fun i:Down (merge h)=> p∈ i.val.choose) hp.symm)|>.trans mem_union
    have hP{p: Pod}(h:p∈x.val.choose): p∈ P.enclosed:=under x.property (stage_in h); have hQ{p: Pod}(h:p∈ y.val.choose): p∈ Q.enclosed:=under y.property (stage_in h)
    have hv(p:Pod)(he:p∈ P.enclosed): p∉ Q.enclosed:=fun hz=> Finset.disjoint_left.mp (Free.enclosed h) he hz
    apply Prod.ext
    · refine Subtype.ext (ext (Finset.ext fun p=> ?_)); change _ ↔ p∈ (portion P R).choose; rw [portion, mem_filter,h1]; specialize hv p; have hP:= @hP p; have hQ:= @hQ p; tauto
    refine Subtype.ext (ext (Finset.ext fun p=>?_)); change _ ↔ p∈ (portion Q R).choose; rw [portion,mem_filter,h1]; specialize hv p; have hP:=@hP p; have hQ:=@hQ p; tauto

def twineEquiv : Down P × Down Q ≃ Down (merge h) := Equiv.ofBijective (twine h) ((bijective_iff_existsUnique (twine h)).mpr (twine_unique h))
end YM.Frontier6.Bouquet.Ensemble
