import YM.Frontier6.Forest.Syntax.Satellite

/-!
# Paying unreduced word bills at one value

Internal gaps wide and one common expense. Finished fragments enter this class when
processing the deepest stratum of a logarithmic tree. No polynomial-in-depths
estimate should be inferred for arity-dependent valuation or perturbation uses.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Forest
open Road Function Set Finset Filter Fareway Spec Tale
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {I V X:Type}{G:Gauge}{C:Family G}{H:Extraction.Order}{S:Table C.book}
inductive Mist (T:Fareway I) (b:ℝ) (P:Fabric I) : Art S I → ℝ → Prop
 | word {V:Type}[Fintype V][DecidableEq V][Nonempty V]{x:I→ V→ E4}(v:V→ S.Tag)(hx: Wide T x b)(hP:Extends T P (sheet x)): Mist T b P (inscription S x v) (load v * b)
 | add {A B w} (a:Mist T b P A w)(b':Mist T b P B w): Mist T b P (A+B) w
 | scale {c:I→ℂ}{u w:ℝ}{A}(hc:T.Costs c u)(h:Mist T b P A w): Mist T b P (fun i=> c i • A i) (u+w)
 | cf {A B w} (h:Mist T b P A w)(he:A=ᶠ[T.via] B): Mist T b P B w
 | mono {A w u}(h:Mist T b P A w)(he:w≤u): Mist T b P A u
 | zero (w): Mist T b P 0 w

namespace Mist
variable {T : Fareway I}{b a q t r:ℝ} {P Q Q':Fabric I} {A B:Art S I}(h: Mist T b P A a)
include h
lemma acts : Intact T P A:= by
    induction h with
    | word v hx hP=> exact (hx.injective.and hP).mono fun i hi=> Acts.step _ hi.1 (fun j=> hi.2 ⟨j,rfl⟩) _
    | add _ _ hi hj=> exact Intact.plus hi hj
    | scale hc h ih=> exact ih.mono fun i hi=> hi.scale _
    | cf h hk ih=> exact (ih.and hk).mono fun i hi=> hi.2 ▸ hi.1
    | mono _ _ ih=> exact ih
    | zero => exact Eventually.of_forall fun _=> Acts.zero
lemma weaker (he:Extends T Q P): Mist T b Q A a:= by
    induction h with
    | word v hx h=> exact word v hx (he.trans h)
    | add _ _ hi hj=> exact hi.add hj
    | scale hc h ih=>exact ih.scale hc
    | cf h hk ih=> exact ih.cf hk
    | mono _ _ ih=> exact ih.mono ‹_›
    | zero=> exact zero _
lemma multiplication (hk:Mist T b Q B q)(he:Cross T P Q b): Mist T b (P⊔Q) (A*B) (a+q):=by
   induction h with
   | word v hx hX =>
      induction hk with
      | word u hy hY=>
          apply Mist.mono (w:=load (Sum.elim v u)*b)
          · have he':= unity hx hy (separate_range (he.mono hX hY))
            refine (word (P:=P⊔Q) (Sum.elim v u) he' ?_).cf ?_
            · refine extends_sheet (fun i=>?_); rcases i with i|i; exacts [extends_left.contains (hX.contains (contains_sheet _ i)),extends_right.contains (hY.contains (contains_sheet _ i))]
            exact Eventually.of_forall fun i=>concatenates _ _ _ _ _
          apply le_of_eq; unfold load σ; rw [Fintype.sum_sum_type]; simp only [Nat.cast_add]; rw [add_mul];rfl
      | add ak bk ih jh=> rw [mul_add]; exact ih.add jh
      | @scale c u' w Z hc h ih=> rw [show load v*b+(u'+w)=u'+(load v*b+w) by ring]; refine (ih.scale hc).cf (Eventually.of_forall fun i=>?_); simp only [Pi.mul_apply,mul_smul_comm]
      | cf h hv ih=> exact ih.cf (Filter.EventuallyEq.mul Filter.EventuallyEq.rfl hv)
      | mono _ hh ih=> exact ih.mono (add_le_add_right hh _)
      | zero=>rw [mul_zero];exact zero _
   | add _ _ ih jh=> rw [add_mul]; exact ih.add jh
   | @scale c u' w Z hc h ih=> rw [add_assoc]; refine (ih.scale hc).cf (Eventually.of_forall fun i=>?_); simp only [Pi.mul_apply,smul_mul_assoc]
   | cf h hk ih=> exact ih.cf (hk.mul Filter.EventuallyEq.rfl)
   | mono h hh ih=> exact ih.mono (add_le_add_left hh _)
   | zero=> rw [zero_mul]; exact zero _
lemma neg : Mist T b P (-A) a:= by
   let f (_:I):= (-1:ℂ); have ht:=h.scale (c:=f) (u:=0) (Fareway.Costs.const _); rw [zero_add] at ht; exact ht.cf (Eventually.of_forall (fun i=>neg_one_smul ..))
lemma sub (he:Mist T b P B a): Mist T b P (A-B) a:= by rw [sub_eq_add_neg]; exact h.add he.neg
omit h
lemma step {x:I→ E4}(v:S.Tag)(hx:Contains T P x): Mist (S:=S) T b P (fun i=>letter S (x i) v) ((v.1:ℝ)*b):= by
   let y(i:I)(_:Unit):= x i; let u (_:Unit):= v; have he:Wide T y b:= fun i j hi=> (hi (Subsingleton.elim ..)).elim
   have ht : inscription S y u=(fun i=>letter S (x i) v):=by ext1 i; unfold inscription assembly; rw [Fintype.prod_unique]
   simpa only [ht, load,Road.σ, Fintype.sum_unique,grades] using (word u he (extends_sheet (fun i=>hx)))
lemma folds {V:Type*} (s:Finset V){A:V→Art S I}(h:∀ i∈s,Mist T b P (A i) a): Mist T b P (fun i=>∑ j∈s,A j i) a:=by
   induction s using Finset.induction_on with
   | empty=>simp only [Finset.sum_empty]; exact zero _
   | @insert i s he ih=> simp_rw [Finset.sum_insert he]; exact (h i (mem_insert_self ..)).add (ih fun i hi=> h _ (mem_insert_of_mem hi))
end Mist
end YM.Frontier6.Forest
