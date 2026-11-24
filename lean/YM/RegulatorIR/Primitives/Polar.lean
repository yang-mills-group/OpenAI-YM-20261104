import YM.RegulatorIR.Primitives.Verse
import YM.RegulatorIR.Cluster.Cross
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Polynomial root jets in t-log coordinate
Combined (coupling, potential field) variables. No uniform differentiation
requirements. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Prim
open Function Budget Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory MvPolynomial Finset Cluster Diagram
open scoped Topology ENNReal BigOperators Classical PowerSeries ContDiff
variable {I J:Type}{k a b:ℕ}
variable [Fintype I] [DecidableEq I]
def Satin (T: Ranked I): Prop:=∀ i, IsSym (T i)

def Mold (k:ℕ)(f:(I→ℝ)→ℝ):Prop:=∃ T:Ranked I, Satin T ∧ Within k T ∧ ∀ x,f x=MvPolynomial.eval x (packed T k)
variable {f g:(I→ℝ)→ℝ}
namespace Mold
omit [DecidableEq I] in
lemma plus (h:Mold k f)(he:Mold k g): Mold k (f+g):=by
 obtain ⟨T,hT,hw,h⟩:=h; obtain ⟨U,hU,hR,he⟩:=he
 refine ⟨T+U,fun i=>symmetric_add (hT i) (hU i),fun i hi=>?_,fun x=>by rw [Pi.add_apply,h,he,pack_add,map_add]⟩
 by_contra! hh
 have hv : T i=0 ∧ U i=0:= ⟨Classical.not_not.mp (fun hg=>(not_le.mpr hh) (hw i hg)), Classical.not_not.mp (fun hg=>(not_le.mpr hh) (hR i hg))⟩
 rw [Pi.add_apply,hv.1,hv.2,add_zero] at hi; contradiction
omit [DecidableEq I] in
lemma tilt (h:Mold k f)(c:ℝ):Mold k (fun i=>c*f i) :=by
 obtain ⟨T,hT,ht,h⟩:=h; refine ⟨c • T, fun i=> symmetric_scale (hT i) _, fun i hi=> ht i (fun he=> hi (by rw [Pi.smul_apply,he,smul_zero])),fun x=> by dsimp only; rw [h,pack_smul,MvPolynomial.eval_mul,MvPolynomial.eval_C]⟩
omit [DecidableEq I] in
lemma inert (n:ℕ)(c:ℝ):Mold n (I:=I) (fun _=>c):=by
 let T: Ranked I:=Pi.single 0 (fun _=>c);refine ⟨T, ?_,?_,?_⟩
 · rintro (i|i)
   · rw [show T 0=(fun _=>c) from Pi.single_eq_same _ _];intro _ _; rfl
   rw [show T (i+1)=0 from Pi.single_eq_of_ne (by omega) _]; exact symmetric_zero
 · intro i hi; by_contra! he; exact hi (Pi.single_eq_of_ne (by omega) _)
 intro x; rw [packed, Finset.sum_eq_single_of_mem 0 (by simp) (fun i _ he=> by rw [show T i=0 from Pi.single_eq_of_ne he _,render_zero]), show T 0=(fun _=>c) from Pi.single_eq_same _ _, render]; simp [word]
omit [DecidableEq I] in
lemma multiplication (h:Mold a f)(he:Mold b g): Mold (a+b) (f*g):= by obtain ⟨T,hT,hw,h⟩:=h; obtain ⟨V,hV,hp,ht⟩:=he;exact ⟨crisp T V,crisp_sym T V,adorns T V hw hp,fun x=>by rw [Pi.mul_apply,h x,ht x,crisp_packed T V hw hp, MvPolynomial.eval_mul]⟩
lemma symbol (i:I): Mold 1 (fun v=>v i):=by
 let W:Tuple I 1:=fun _=>i; let t:Packet I 1:= Pi.single W (1:ℝ); let T: Ranked I:=Pi.single 1 t
 refine ⟨T,?_,fun j hj=>by by_contra! hg; exact hj (Pi.single_eq_of_ne (by omega) _),fun x=>?_⟩
 · intro j; by_cases h:j=1
   · subst j; intro e v; rw [Subsingleton.elim e (Equiv.refl _)];rfl
   rw [show T j=0 from Pi.single_eq_of_ne h _];exact symmetric_zero
 rw [packed,sum_eq_single_of_mem 1 (by decide) (fun j _ he=> by rw [show T j=0 from Pi.single_eq_of_ne he _,render_zero]),show T 1=t from Pi.single_eq_same _ _, render]
 rw [sum_eq_single_of_mem W (mem_univ W)]; simp only [word,t, Pi.single_eq_same,MvPolynomial.eval_mul,MvPolynomial.eval_C,map_prod,MvPolynomial.eval_X]; simp [W]
 intro j _ hv; rw [show t j=0 from Pi.single_eq_of_ne hv _,map_zero,zero_mul]
-- sum/products
omit [DecidableEq I] in
lemma sigma (s:Finset J)(f:J→(I→ℝ)→ℝ)(h:∀ i∈s,Mold k (f i)): Mold k (∑ i∈s,f i):=by
 induction s using Finset.induction_on with
 | empty =>rw [sum_empty]; exact inert _ _
 | insert i s he ih =>rw [sum_insert he];exact plus (h i (mem_insert_self ..)) (ih (fun _ hh=>h _ (mem_insert_of_mem hh)))
omit [DecidableEq I] in
lemma prods (s:Finset J)(f:J→ (I→ℝ)→ℝ)(h:∀ i∈s,Mold 1 (f i)): Mold s.card (∏ i∈s,f i):=by
 induction s using Finset.induction_on with
 | empty =>simp only [Finset.prod_empty]; exact inert _ _
 | insert i s he ih=> rw [prod_insert he, card_insert_of_notMem he,add_comm]; exact multiplication (h i (mem_insert_self ..)) (ih (fun _ hh=>h _ (mem_insert_of_mem hh)))
end Mold

abbrev Figure (I:Type):= ℝ × (I→ℝ)
private def rodP (i:Option I) (w:I→ℝ):= i.elim 1 w
private def poleP (i:Option I): Figure I := i.elim (1,0) (fun j=>(0,Pi.single j 1))
private lemma rodV (z: Option I) : Mold 1 (rodP z):=by cases z <;> first|exact Mold.inert ..|exact Mold.symbol _
private lemma rods (w:I→ℝ) : (1,w)=∑ i: Option I,rodP i w • poleP i:=by
 apply Prod.ext
 · simp_rw [Prod.fst_sum]; simp [Fintype.sum_option, poleP,rodP]
 rw [Prod.snd_sum]; ext1 i; simp [Fintype.sum_option,poleP,rodP, Finset.sum_apply, Pi.single_apply,mul_ite]
lemma mold_jet (F:Figure I→ℝ)(k:ℕ): Mold k fun v=>jet F k (1,v):=by
 let D := (iteratedFDeriv ℝ k F 0).toMultilinearMap
 let c:ℝ:=(k.factorial:ℝ)⁻¹
 let T (z: Tuple (Option I) k):= c*D (poleP ∘ z)
 let q(z:Tuple (Option I) k)(v:I→ℝ):=T z*(∏ i,rodP (z i) v)
 have hp : ∀ v:I→ℝ,jet F k (1,v)= (∑ z:Tuple (Option I) k,q z) v:=by
    intro v; change c*D (fun _=>(1,v))= _
    rw [rods,show D _= _ from (D.map_sum (fun _ i=> rodP i v • poleP i)),mul_sum,Finset.sum_apply]
    apply Finset.sum_congr rfl;intro z _; have hh:=D.map_smul_univ (fun i=>rodP (z i) v) (fun i=>poleP (z i));rw [hh]; unfold q T; simp only [smul_eq_mul]; change _= c*D (fun i=>poleP (z i))*_; ring
 rw [funext hp]; apply Mold.sigma; intro i _
 have hq:=Mold.prods univ (fun j:Fin k=>rodP (i j)) (fun _ _=> rodV _)
 rw [card_univ,Fintype.card_fin] at hq
 convert Mold.tilt hq (T i) using 1; ext x; simp [q]
end YM.RegulatorIR.Prim
