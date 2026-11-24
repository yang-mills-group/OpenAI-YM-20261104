import YM.Frontier6.Forest.Tents.Canvas

/-!
# Support footprint of a spelling
Permit only finite linear combinations of assemblies legitimately on every
companion term's stated physical patch. Unit syntax 1 is an empty collection,
not a unit cancellation through a collision.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Forest
open Road Function Set Filter Fareway Spec Tale
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {I V X:Type}{T:Fareway I}{G:Gauge}{C:Family G}{H:Extraction.Order}{S:Table C.book}
inductive Acts (P:Set E4) : Spelling S→ Prop
| step {V:Type}[Fintype V] (x:V→ E4)(hx:Injective x)(hp:∀ i,x i∈ P)(v:V→ S.Tag): Acts P (assembly S x v)
| zero : Acts P 0
| add {A B}(a:Acts P A)(b: Acts P B):Acts P (A+B)
| scale (c:ℂ){A}(a:Acts P A): Acts P (c • A)
namespace Acts
variable {P Q Q':Set E4}{A B:Spelling S}(h: Acts P A)
include h
lemma sub (he:Acts P B):Acts P (A-B):=by rw [sub_eq_add_neg,← neg_one_smul ℂ]; exact h.add (he.scale _)
lemma weaker (he:P ⊆ Q): Acts Q A:=by induction h with
    | step x hx hp v=> exact step x hx (fun i=> he (hp i)) v
    | zero=> exact zero
    | add _ _ ih jh=> exact ih.add jh
    | scale c _ ih=> exact ih.scale _
lemma mul (he: Acts Q B)(hp:Disjoint P Q): Acts (P∪Q) (A*B):=by
   induction h with
   | step x hx hP v=>
      induction he with
      | step y hy hQ u=>
         rw [← concatenates]; apply step
         · rintro (i|i) (j|j) hh
           exacts [congr_arg _ (hx hh), (Set.disjoint_left.mp hp (hP _) ((show x i=y j from hh) ▸ hQ j)).elim,(Set.disjoint_left.mp hp (hP j) ((show x j=y i from hh.symm) ▸ hQ i)).elim, congr_arg _ (hy hh)]
         rintro (i|i); exacts [Or.inl (hP i),Or.inr (hQ i)]
      | zero=> rw [mul_zero]; exact zero
      | add _ _ h i=>rw [mul_add]; exact h.add i
      | scale c _ ih=>rw [mul_smul_comm]; exact ih.scale _
   | zero=>rw [zero_mul]; exact zero
   | add _ _ h i=> rw [add_mul]; exact h.add i
   | scale c _ ih=> rw [smul_mul_assoc]; exact ih.scale _
lemma visible (K:Final C H S) {x:E4}{r:ℝ}{d:ℕ}(he:Frontier6.Safe K d r) (hy:∀ y∈P,‖y-x‖≤r): Visible K x d A:=by
   induction h with
   | step y he' hp v=> exact visibles K _ he he' (fun i=>hy _ (hp i)) v
   | zero=> exact Visible.zero K
   | add _ _ a b=> exact a.plus K b
   | scale c _ ih=> exact ih.scale K _
omit h
lemma sum (s:Finset X)(f:X→ Spelling S)(h:∀ i∈s,Acts P (f i)): Acts P (∑ i∈s,f i):=by induction s using Finset.induction_on with
   | empty=> rw [Finset.sum_empty]; exact zero
   | @insert i s he ih=> rw [Finset.sum_insert he]; exact (h _ (Finset.mem_insert_self ..)).add (ih (fun i hi=> h i (Finset.mem_insert_of_mem hi)))
lemma one : Acts P (1:Spelling S):= by simpa only [assembly,Finset.univ_eq_empty, Finset.prod_empty] using step (P:=P) (fun _:Empty=>(0:E4)) (fun i=> i.elim) (fun i=> i.elim) (fun i=>(Empty.elim i:S.Tag)) -- syntax
lemma letter {x:E4}(h:x∈ P)(v:S.Tag): Acts P (Tale.letter S x v):=by simpa only [assembly,Fintype.prod_unique] using step (fun _:Unit=>x) (fun _ _ _=> rfl) (fun _=> h) (fun _:Unit=>v)
lemma suit (K: Final C H S){x:E4}(h:x∈P)(d:ℕ)(f:S.Field d): Acts P (Tale.suit K x d f):=by rw [suit_eq]; exact sum _ _ (fun i _=> scale _ (letter h _))
lemma deck (K: Final C H S){x:E4}(h:x∈P)(d:ℕ)(f:S.Field d): Acts P (Tale.deck K x d f):=by rw [deck_eq]; exact sum _ _ (fun i _=> suit K h _ _)
end Acts

-- projection spellings. `All` and `reject` always act on the same centered input.
variable (K:Final C H S)
def all (x:E4) (d:ℕ) (A:Spelling S):=deck K x d (absorb K x d A)
def pitch (x:E4) (w:ℕ)(A:Spelling S):= weight K w (absorb K x w A)
def part (x:E4) (w:ℕ)(A:Spelling S):= suit K x w (pitch K x w A)
def reject (x:E4) (d:ℕ)(A:Spelling S):= A-all K x d A
-- later all K here through inclusive horizon. no-projection when negative separate.
end YM.Frontier6.Forest
