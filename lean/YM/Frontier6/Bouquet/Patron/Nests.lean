import YM.Frontier6.Bouquet.Patron.Staging

/-! Multilinearity at boundaries and grouping algebra on the same tasks. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet
open Function Set Finset Ensemble MeasureTheory Normal Filter Road Forest Tale Spec
open scoped Topology BigOperators Classical InnerProductSpace lp ContDiff Matrix.Norms.Frobenius
open scoped YM.Frontier6.Bouquet
variable {I V:Type}{G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}
variable {Y:Type*}[AddCommGroup Y][Module ℂ Y]{P Q R:Ensemble}
abbrev Program (S:Table C.book)(I:Type) := I→ Spelling S
abbrev Patron (S:Table C.book)(V:Type)(Y:Type*) [AddCommGroup Y][Module ℂ Y]:= MultilinearMap ℂ (fun _:V=> Spelling S) Y
-- A linear question constructor at one group (not removing remaining singleton positions)
def hearing (p:Pod)(A:Spelling S →ₗ[ℂ] Y): Patron S (only p) Y:= A.compMultilinearMap (MultilinearMap.mkPiAlgebra ℂ (only p) (Spelling S))
lemma hearing_at (p:Pod)(A:Spelling S →ₗ[ℂ] Y)(v:Program S (only p)) : hearing p A v=A (v default):=by rw [hearing,LinearMap.compMultilinearMap_apply,MultilinearMap.mkPiAlgebra_apply,Fintype.prod_unique]
def dialogues (h:P ≤ Q)(v:Q): Finset P:= Finset.univ.filter (fun i=> assign h i=v)
def garland (h:P≤ Q)(v:Program S P)(i:Q):=∏ x∈dialogues h i,v x
-- sigma incarnation and coherence
abbrev dialogues_equiv (h:P ≤ Q) := Equiv.sigmaFiberEquiv (assign h)
variable (h:P ≤ Q) (A: Patron S Q Y)(v: Program S P)
def convey : Patron S P Y:=
   let y:= A.compMultilinearMap (fun i:Q=> MultilinearMap.mkPiAlgebra ℂ ({x:P// assign h x=i}) (Spelling S))
   MultilinearMap.domDomCongr (dialogues_equiv h) y
lemma convey_at : convey h A v=A (garland h v):=by
    let y(i:Q):=∏ x:{x:P// assign h x=i}, v x.val; change A y=A (garland h v); apply congr_arg A; ext1 i; exact (Finset.prod_subtype (dialogues h i) (p:=fun x:P=> assign h x=i) (fun i=>by simp [dialogues]) v).symm
lemma members (i j) : i∈ dialogues h j ↔ assign h i=j:=by simp [dialogues]
lemma members' (i j) : i∈ dialogues h j ↔ (i:P).val≤ (j:Q).val:=⟨fun he=> members h i j|>.mp he ▸ inside h i, fun hu=> (members h i j).mpr (assigned h i j hu)⟩ -- syntax
lemma garnet (g:Q≤R): garland (h.trans g) v=garland g (garland h v):=by
   ext1 i; unfold garland; let D:= (dialogues g i).biUnion (dialogues h); have he:dialogues (h.trans g) i=D:=by
       ext1 j; rw [members, via h g, show _∈D↔ _ from mem_biUnion]; simp_rw [members]; simp [eq_comm] -- check
   rw [he]; apply Finset.prod_biUnion; intro j _ k _ hj; exact Finset.disjoint_left.mpr fun x ha hb=>hj (((members ..).mp ha).symm.trans ((members ..).mp hb))
lemma conveys (g:Q ≤ R)(A:Patron S R Y) : convey (h.trans g) A= convey h (convey g A):=by ext1 m; simp_rw [convey_at]; rw [garnet]
lemma dialogues_self (i:P): dialogues (le_refl P) i={i}:=by ext1 j;rw [members,assigned (le_refl P) j j le_rfl]; simp
lemma dialogueSolo {Q:Pod}(v:P≤only Q)(j:only Q) : dialogues v j=Finset.univ:=by ext1 i; simp only [members,Finset.mem_univ]; exact ⟨fun _=>trivial,fun _=>Subsingleton.elim ..⟩
lemma garland_alone (v:Program S P):garland (le_refl P) v=v:=by ext1 i; rw [garland, dialogues_self,Finset.prod_singleton]
end YM.Frontier6.Bouquet
