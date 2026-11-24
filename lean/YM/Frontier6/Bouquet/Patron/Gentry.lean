import YM.Frontier6.Bouquet.Patron.Nests

/-! Recognition at the support points of the kernels. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet
open Function Set Finset Ensemble MeasureTheory Normal Filter Road Forest Tale Spec
open scoped Topology BigOperators Classical InnerProductSpace lp ContDiff Matrix.Norms.Frobenius
open scoped YM.Frontier6.Bouquet
variable {I V:Type}{G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}
variable {Y:Type*}[TopologicalSpace Y][AddCommGroup Y][Module ℂ Y]{P Q:Ensemble}

-- arbitrary factors including empty collections. separate only when multiplying.
lemma Appears.product {D:Set E4}[TopologicalSpace I](s:Finset V)(A: V→ Set E4) {X:V→Art S I} {x:I}(he:∀ i∈s,A i⊆D)(h:∀ i∈s,Appears (A i) x (X i))(hv:(s:Set V).PairwiseDisjoint A): Appears D x (fun i=>∏ j∈s,X j i):=by
   induction s using Finset.induction_on generalizing D with
   | empty=>simp only [Finset.prod_empty]; exact Appears.one
   | @insert i s hi ih=>
       let U := ⋃ i∈s,A i; rw [funext (fun k:I=>prod_insert hi (f:=fun j:V=> X j k))]; -- syntax undone
       have ht : Disjoint (A i) U:= Set.disjoint_iUnion_right.mpr fun j=> Set.disjoint_iUnion_right.mpr fun (hj:j∈s)=> hv (Finset.mem_insert_self ..) (Finset.mem_insert_of_mem hj) (by rintro rfl; contradiction)
       have hJ(j:V)(hj:j∈s): j∈ insert i s:= mem_insert_of_mem hj
       refine ((h i (mem_insert_self ..)).mul (ih (D:=U) ?_ (fun j hj=> h j (hJ j hj)) ?_) ht).weaker (Set.union_subset (he i (mem_insert_self ..)) (Set.iUnion_subset fun j=>Set.iUnion_subset fun hj=> he j (hJ j hj)))
       · intro j hj; exact subset_iUnion₂ (s:=fun j (_:j∈s)=> A j) j hj
       intro j hj k hk he; exact hv (hJ j hj) (hJ k hk) he
-- program evaluations regular with respect to spellings when points legitimately
-- in the prescribed box, independently before evaluating any μ weights
def Gentle (g:Patron S P Y)(A: Balcony P) : Prop:=∀ {I:Type}[TopologicalSpace I] (i:I) (v:P→ Art S I), (∀ j:P,Appears (A j) i (v j))→ ContinuousAt (fun a:I=>g (fun j=>v j a)) i
lemma Gentle.lesser {g:Patron S P Y}{A B: Balcony P}(he: Gentle g A)(hx:B≤A): Gentle g B:=fun i v h=> he i v (fun j=> (h j).weaker (hx j)) -- implicit instances lambda?
lemma Gentle.refines {g:Patron S P Y}{A:Balcony P}(he:Gentle g A)(h:Q≤P){B: Balcony Q}(hk:B ≤ A ∘ assign h)(hD:∀ i:P,((dialogues h i:Set Q)).PairwiseDisjoint B): Gentle (convey h g) B:=by
    intro I _ i v hV
    let f(z:P)(x:I):= garland h (fun i=>v i x) z; simp_rw [convey_at]; exact he i f (fun z=>Appears.product (dialogues h z) B (fun j hj=> by simpa only [members h j z|>.mp hj] using (show B j⊆ A (assign h j) from hk j)) (fun j _=> hV j) (hD _))
lemma Gentle.modify {g:Patron S P Y}{A B: Balcony P}(he: Gentle g A) (K:P→Spelling S→ₗ[ℂ] Spelling S)
    (hk: ∀ i:P,∀ {I:Type}[TopologicalSpace I] (x:I) (p: I→ Spelling S), Appears (B i) x p→Appears (A i) x (K i ∘ p)) : Gentle (g.compLinearMap K) B:=by
    intro I _ x v hv; exact he x (fun j i=>K j (v j i)) (fun j=> hk j x (v j) (hv j))
lemma Gentle.hearing (P:Pod)(g:Spelling S→ₗ[ℂ] Y){A: Balcony (only P)} (h:∀ {I:Type}[TopologicalSpace I](x:I)(v:I→Spelling S),Appears (A default) x v → ContinuousAt (g ∘ v) x): Gentle (Bouquet.hearing P g) A:=by
    intro I _ i v hV; simp_rw [hearing_at]; exact h i (v default) (hV default)
section
variable (A: Patron S P Y)
def transaction (i:P)(R:Spelling S→ₗ[ℂ] Spelling S): Patron S P Y:= A.compLinearMap fun j=>if j=i then R else LinearMap.id
omit [TopologicalSpace Y] in
lemma transactions (i:P)(R:Spelling S→ₗ[ℂ] Spelling S)(p:Program S P): transaction A i R p=A (Function.update p i (R (p i))):=by
    unfold transaction; rw [MultilinearMap.compLinearMap_apply]; congr 1; ext1 j; by_cases he:j=i; subst j; simp [Function.update_self]; simp only [if_neg he, Function.update_of_ne he,LinearMap.id_apply]
omit [TopologicalSpace Y] in
lemma ticket (i:P)(R:Spelling S→ₗ[ℂ] Spelling S)(p:Program S P): transaction A i R p=A.toLinearMap p i (R (p i)):=by rw [transactions]; rfl
end
end YM.Frontier6.Bouquet
