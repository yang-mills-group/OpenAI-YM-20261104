import YM.RG3.Script.Engrave
/-! # Pair old strand and model strand, registering an actual operation for
Script.Marker. Preserves exact reference and excludes properly even on zeros.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Script
open Function Lattice RG Wilson Overlay Marker RG3.Forms RG3.Render RG3.Press Ac Extra.Multi Push.AbsoluteSums MeasureTheory Extra.Iteration Source Push.Local Estate Finset
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {n:Side} {V:Type*} [Fintype V] [DecidableEq V]{R:Census V}{ζ:V→Site n}{G:Gauge}
  (e : Edition ζ R G) {A : Estate n R}
namespace Edition

def negative : Edition ζ R G where
  pure:=-e.pure
  home:=e.home
  pins:=e.pins
  song i:=-e.song i
  footer:={e.footer with value:=-e.footer.value}

omit [Fintype V] in
lemma masked_neg (a : Config G n→ℂ)(U : Config G n)(x : ℝ)(X : Support n):
    masked x X (-a) U= -masked x X a U:= by unfold masked Set.indicator; split <;> simp
 omit [Fintype V] in
lemma send_neg (x : R.Mode)(a : ℂ):Poly.send x (-a) = -Poly.send x a:=by
  ext; simp only [Poly.part_neg,Poly.part_send]; split <;> simp
lemma log_neg (p : BudgetPoint)(U : Config G n):e.negative.log p U= - e.log p U:=by
  unfold log birth Captions.chord negative
  simp only [Pi.neg_apply]; simp_rw [masked_neg,send_neg,Finset.sum_neg_distrib,tsum_neg]; abel

omit [Fintype V] in
lemma principle_negative {p}(h:e.Principle p) : e.negative.Principle p:= by
  refine ⟨h.hot,h.rem,fun i=>?_,⟨h.vertical.card,h.vertical.pins⟩⟩
  simpa [negative] using Next.Foundations.regular_smul (-1:ℂ) (h.reg i)
omit [Fintype V] in
lemma grant_negative {p w a u c v f}(he:e.Grant p w a u c v f):e.negative.Grant p w a u c v f:= by
  refine ⟨fun i=>?_,he.nn,fun i j hi=>?_,he.more,fun i=>?_⟩
  · simpa only [negative,Pi.neg_apply,norm_neg] using he.one i
  · simpa [negative] using Next.Foundations.bound_smul (-1:ℂ) (he.pay i j hi)
  simpa [negative] using he.captions i
end Edition

namespace Estate.Truss
variable {e} {ι I : Type*}(t : A.Truss ι G) (s : A.Truss I G)

def versus : A.Truss (ι⊕I) G where
  filing := Sum.elim t.filing s.filing
  notice := Sum.elim t.notice s.notice
  veiled := Sum.elim t.veiled s.veiled
  song := Sum.elim t.song (fun i=> -s.song i)
  shifted i := by cases i with
    | inl i=> exact t.shifted i
    | inr i=> exact s.shifted i

omit [Fintype V] in
lemma paired (h : t.Laws ζ)(h':s.Laws ζ): (t.versus s).Laws ζ := by
  constructor <;> rintro (i|i)
  · exact h.loc _
  · exact fun U V h=>congrArg Neg.neg (h'.loc i U V h)
  · exact h.Borel _
  · exact (h'.Borel _).neg
  · exact h.invariant _
  · exact fun k U=> congrArg Neg.neg (h'.invariant i k U)
  · exact h.pins _
  intro U j he; exact h'.pins i U j (fun H=>he (by change - s.song i U=0; simp [H]))

omit [Fintype V] in
lemma reel_p (p : BudgetPoint)(U : Config G n)(i): ((t.versus s).strand p).payload (Sum.inr i) U= -(s.strand p).payload i U := by
  change reads _ _ _ _=-reads _ _ _ _; unfold reads; dsimp only [versus,Sum.elim_inr]; split; exact Edition.masked_neg ..; rfl

variable {p : BudgetPoint}{w : V→ℝ}{a c d:ℝ}{f:ι→ℝ}{g:I→ℝ}
omit [Fintype V] in
lemma strap_plus (h:t.Strap w p a c f)(h':s.Strap w p a d g):
    (t.versus s).Strap w p a (c+d) (Sum.elim f g) := by
  constructor <;> [rintro (i|i);rintro (i|i) U; intro i]
  · exact h.nonneg _
  · exact h'.nonneg _
  · exact h.here i U
  · change ‖((t.versus s).strand p).payload (.inr i) U‖≤g i; rw [reel_p,norm_neg]; exact h'.here _ _
  exact Cost.sum (h.fromLabel i) (h'.fromLabel i)

section cut
open Edition
variable {c c' : Crew V}{e':Edition ζ R G}(r : Edition.Size e c A)(v:Edition.Size e' c' A)
  {a a' u u' Z Y δ δ' :ℝ}{f f' : ℕ→ℝ}(hw : ∀ i,0<w i)
  (h:e.Principle p)(h':e'.Principle p)(hb:e.Grant p w a u δ Z f)(hb':e'.Grant p w a' u' δ' Y f') (ha:p.supportExponent ≤ a)(hα:p.supportExponent ≤ a')

include hw h h' hb hb' ha hα r v
theorem conserved:
    let F:=(cutting r).versus (cutting v)
    let g:=(keep e c).add ((keep e' c').negative)
    e.log p=e'.log p+g.log p+(F.strand p).tally:=by
  intro F g; ext1 U
  let I :=(Edition.cutting r).strand p; let N:= (Edition.cutting v).strand p
  have hh:= Reg.choir U hw h hb ha
  have hn:= Reg.choir U hw h' hb' hα
  have hI:Summable (fun i=>I.reel i U) := by simp_rw [show ∀i,I.reel i U= _ from cutfit r p U]; exact hh.summable.comp_injective Subtype.val_injective
  have hN:Summable (fun i=>N.reel i U) := by simp_rw [show ∀i,N.reel i U= _ from cutfit v p U]; exact hn.summable.comp_injective Subtype.val_injective
  let T i:= (F.strand p).reel i U
  have he : (F.strand p).tally U= I.tally U-N.tally U:=by
    have h₁: Summable (fun i=>T (Sum.inl i)):=hI
    have hz: (fun i=>T (Sum.inr i))=(fun i=> - N.reel i U):=by
      funext i; unfold T Stage.Trace.reel; rw [show _ =_ from reel_p _ _ _ _ i, send_neg]; rfl -- `_=_` may infer
    change tsum T=_
    rw [Summable.tsum_sum (f:=T) h₁ (show Summable (fun i=>T (Sum.inr i)) by rw [hz]; exact hN.neg),show (fun i=> T (.inr i))=_ from hz,tsum_neg]; rfl
  let S:= keep e c; let X:= keep e' c'
  have hS:= living hw (keeps _ c h) (keep_price c hw h hb) ha U
  have hX:= living hw (principle_negative X (keeps _ c' h')) (grant_negative X (keep_price c' hw h' hb')) hα U
  change _= e'.log p U+_+(F.strand p).tally U
  rw [he,show g.log p U=S.log p U+X.negative.log p U from log_plus p U hS.1 hX.1 hS.2 hX.2, X.log_neg,etch r U hw h hb ha,etch v U hw h' hb' hα]; abel
end cut
end Estate.Truss
end YM.RG3.Script
