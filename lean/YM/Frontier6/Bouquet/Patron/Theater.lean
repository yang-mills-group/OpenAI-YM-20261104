import YM.Frontier6.Bouquet.Gate.Contacting
import YM.Frontier6.Forest.Pen.Pinnacle
/-!
# Legitimacy and regularity of applications of the polynomial symbols.
 Actual consumers of an expression have continuity on appearances as below;
 footprints checked at the `ContinuousAt` position. Bounds/cost requirements
 for summing on shrinking charts separate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet
open Function Set Finset Ensemble MeasureTheory Normal Filter Road Forest Tale Spec
open scoped Topology BigOperators Classical InnerProductSpace lp ContDiff Matrix.Norms.Frobenius
open scoped YM.Frontier6.Bouquet
variable {I V X:Type}{G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}
inductive Appears [TopologicalSpace I](P:Set E4)(x:I): Art S I→ Prop
| say {V:Type}[Fintype V][DecidableEq V]{y:I→ V→ E4}(v:V→ S.Tag)(hc:ContinuousAt y x)(he:Injective (y x))(hp:Set.range (y x) ⊆ P): Appears P x (inscription S y v)
| cf {A B}(a:Appears P x A)(h:A=ᶠ[𝓝 x] B): Appears P x B
| vac : Appears P x 0
| add {A B}(h:Appears P x A)(he:Appears P x B): Appears P x (A+B)
| scale {A}(h:Appears P x A){p:I→ℂ}(he:ContinuousAt p x): Appears P x (fun i=> p i • A i)
namespace Appears
variable {A B:Art S I}[TopologicalSpace I]{P Q:Set E4}{x:I}(h:Appears P x A)
include h
lemma act : Acts P (A x):=by
    induction h with
    | say v _ he hp=>exact Acts.step _ he (fun i=>hp ⟨i,rfl⟩) _
    | cf h k ih=> exact k.eq_of_nhds ▸ ih
    | vac=> exact Acts.zero
    | add _ _ ih jh=> exact ih.add jh
    | scale h he ih=> exact ih.scale _
lemma previous {J:Type}[TopologicalSpace J]{f:J→I}{y:J}(hh:f y=x)(hf:ContinuousAt f y): Appears P y (A ∘ f):=by
    induction h with
    | @say V _ _ q v hc he hp=> exact say (y:=fun i=> q (f i)) v (hc.comp_of_eq hf hh) (by rw [hh]; exact he) (by rw [hh]; exact hp)
    | cf h he ih=> exact ih.cf (he.comp_tendsto (hh ▸ hf : Tendsto f _ (𝓝 x)))
    | vac=> exact vac
    | add _ _ ih jh=> exact ih.add jh
    | scale _ he ih=> exact ih.scale (he.comp_of_eq hf hh)
lemma weaker (he:P⊆Q) : Appears Q x A:=by induction h with
    | say v hx hp h=> exact say v hx hp (h.trans he)
    | cf a b ih=> exact ih.cf b
    | vac=> exact vac
    | add a b ih jh=> exact ih.add jh
    | scale v h ih=> exact ih.scale h
lemma pays (he: Appears P x B): Appears P x (A-B):=by rw [sub_eq_add_neg]; exact h.add ((he.scale (continuousAt_const (y:=(-1:ℂ)))).cf (Eventually.of_forall fun i=>by simp))
lemma mul (he:Appears Q x B)(hp: Disjoint P Q): Appears (P∪Q) x (A*B):=by
    induction h with
    | @say V _ _ y v hc hy hV =>
       induction he with
       | @say W _ _ z w hk hz hW=>
          let q(i:I):V ⊕ W→E4:= Sum.elim (y i) (z i); have hq:ContinuousAt q x:=continuousAt_pi.mpr fun i=>by rcases i with i|i; exacts [(continuous_apply i).continuousAt.comp hc,(continuous_apply i).continuousAt.comp hk]
          have ht : Injective (q x) :=by rintro (i|i) (j|j) hi; exacts [ congr_arg _ (hy hi), (Set.disjoint_left.mp hp (hV ⟨i,rfl⟩) (hW ⟨j,hi.symm⟩)).elim,(Set.disjoint_left.mp hp (hV ⟨j, rfl⟩) (hW ⟨i,hi⟩)).elim,congr_arg _ (hz hi)]
          have hv : Set.range (q x) ⊆ P∪Q:=by rintro a ⟨i|j,rfl⟩; exacts [Or.inl (hV ⟨i,rfl⟩),Or.inr (hW ⟨j,rfl⟩)]
          exact (say (Sum.elim v w) hq ht hv).cf (Eventually.of_forall fun i=> concatenates ..)
       | cf h hk ih=> exact ih.cf (Filter.EventuallyEq.rfl.mul hk)
       | vac=> rw [mul_zero]; exact vac
       | add _ _ ih jh=> rw [mul_add]; exact ih.add jh
       | scale v' h ih=> exact (ih.scale h).cf (Eventually.of_forall fun i=>(mul_smul_comm ..).symm)
    | cf h' hz ih=> exact ih.cf (hz.mul Filter.EventuallyEq.rfl)
    | vac=> rw [zero_mul]; exact vac
    | add _ _ ih jh=> rw [add_mul]; exact ih.add jh
    | scale _ h ih=> exact (ih.scale h).cf (Eventually.of_forall fun i=> (smul_mul_assoc ..).symm)
omit h
lemma only {y:I→ E4}(v:S.Tag)(hx:ContinuousAt y x)(hp:y x∈ P): Appears P x (fun i=> Tale.letter S (y i) v):=by
   let q(i:I)(_:Unit):=y i; have ht: Set.range (q x)⊆ P:=by rintro y ⟨i,h⟩; exact h ▸ hp
   exact (say (fun _:Unit=>v) (show ContinuousAt q x from continuousAt_pi.mpr fun _=>hx) (fun i j _=> rfl) ht).cf (Eventually.of_forall fun i=>by unfold inscription assembly; rw [Fintype.prod_unique])
lemma sum {A:V→Art S I}(s:Finset V)(he:∀ v∈s,Appears P x (A v)): Appears P x (fun i=>∑ j∈s,A j i):=by
   induction s using Finset.induction_on with
   | empty=> simp only [Finset.sum_empty]; exact vac -- defeq
   | @insert i s hp ih=> simp_rw [Finset.sum_insert hp]; exact (he _ (mem_insert_self ..)).add (ih fun j hj=> he j (mem_insert_of_mem hj))
lemma suit {d:ℕ}{v:I→ S.Field d}{y:I→ E4}(K:Final C F S)(he:ContinuousAt y x)(hp:y x∈ P)(hv:ContinuousAt v x): Appears P x (fun i=> Tale.suit K (y i) d (v i)):=by
   simp_rw [suit_eq]; apply Appears.sum; intro i _; exact (only ⟨d,(marker K d i).val⟩ he hp).scale (((marker K d).coord i ∘ₗ face K d).continuous_of_finiteDimensional.continuousAt.comp hv)
lemma deck {d:ℕ}{v:I→ S.Field d}{y:I→ E4}(K:Final C F S)(he:ContinuousAt y x)(hp:y x∈ P)(hv:ContinuousAt v x): Appears P x (fun i=> Tale.deck K (y i) d (v i)):=by simp_rw [deck_eq]; exact Appears.sum Finset.univ (fun i _=> suit K he hp ((reach K d i).continuous.continuousAt.comp hv))
lemma one : Appears P x (1:Art S I):=by
   apply (say (P:=P) (S:=S) (fun i:Empty=> Empty.elim i) (continuousAt_const (x:=x) (y:=fun _:Empty=> (0:E4))) (fun i=>Empty.elim i) (by rintro u ⟨a,_⟩; exact Empty.elim a)).cf; refine Eventually.of_forall fun i=>?_ ; unfold inscription assembly; rw [univ_eq_empty,Finset.prod_empty];rfl
include h
lemma polls (K:Final C F S)(s:StateIndex K): ContinuousAt (polled K (fun _=>s) A) x:=by
   induction h with
   | say v hx hp h=> exact assembly_cont K s hx hp v
   | cf _ hk ih=> exact ih.congr (hk.mono fun i hi=> congr_arg (poll S _) hi)
   | add _ _ ih jh=> exact (ih.add jh).congr (Eventually.of_forall fun _=> (map_add (poll S _) _ _).symm)
   | scale h hc ih=> exact (hc.smul ih).congr (Eventually.of_forall fun i=> (map_smul (poll S _) _ _).symm)
   | vac=> exact continuousAt_const
end Appears
end YM.Frontier6.Bouquet
