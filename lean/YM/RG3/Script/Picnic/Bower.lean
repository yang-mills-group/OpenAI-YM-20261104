import YM.RG3.Script.Picnic.Cadre
/-!
# Uniform K difference & H/caption vouchers on a common external test family
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Script.Picnic
open Function Lattice RG Wilson Marker Overlay RG3.Forms RG3.Press RG3.Held RG3.Ink
  Extra.Multi Ac Push.AbsoluteSums MeasureTheory Push.Corrected Finset Extra.Iteration
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {n : Side}{V : Type} [DecidableEq V]{R:Census V}{ζ : V→Site n}{G : Gauge}
  {X : Type*}{P : Rep G n}[Nonempty X] (d o : Taste X ζ P R)(T : X→Edition ζ R G)

def balance : Taste X ζ P R := {
    endorse d T with
      menu:= { (endorse d T).menu with
        marks i:= Edition.blend (d.menu.marks i) (o.menu.marks i)
        force x i:= Edition.blend (d.menu.force x i) (-o.menu.force x i) }
      root:= d.root }

lemma even (h:Firm T)(x:X) : (balance d o T).leaf x=Edition.jetty (d.leaf x) (o.leaf x) (T x):= by
  have he:= endorsed_eq d h x
  let U : Deck R P→Deck R P:= fun S=>{
    S with
      contents:= {
        S.contents with
          marks := (balance d o T).menu.marks
          entries := (balance d o T).menu.force x } }
  exact congrArg U he
private def numberX : ℕ × ℕ ≃ (ℕ×ℕ)⊕(ℕ×ℕ):= (Equiv.prodCongr (Equiv.refl ℕ) (numbering (ℕ⊕ℕ))).trans (Equiv.prodSumDistrib ..)
lemma coins {w:V→ℝ}{a u v Y:ℝ}{f g:ℕ→ℝ}(h:Voucher T P.p w a u v Y f g)(ha:P.p.supportExponent ≤ a)
    {iu ic ig b iA ju jc jg jA:ℝ}(hd:d.Snacks w iu ic ig b iA)(ho:o.Snacks w ju jc jg b jA):
    Nonempty ((balance d o T).Snacks w u v (ig+jg) b Y):=by
  let C:=balance d o T
  have hC := even d o T h.toFirm
  let t (i:ℕ×ℕ):=Edition.blend (fun j=>hd.strong.black (i.1,j)) (fun j=>ho.strong.black (i.1,j)) i.2
  have he := h.ease hd.strong.radii ha
  let z:=Classical.arbitrary X
  have hV x := Edition.lyric _ _ (h.stays x) (d.snack hd x).1 (o.snack ho x).1 d.root o.root
  have hx' x : (C.menu.terms x).Active:= by
    change ( (C.leaf x).contents).Active
    rw [hC x]; exact (hV x).articles
  refine ⟨⟨f,t,hx',hd.strong.radii,hd.strong.divisor, fun i=> (h.backs i).one,fun i=>?_, (he.backs z).more,fun i j=>?_,fun i=>?_⟩,fun x=>?_,g,h.fiscal,he.ticket z⟩
  · refine ⟨(h.backs z).nn _,fun x s hi=>?_⟩
    rw [C.root,show C.menu.branch i= _ from congrFun (h.home z x) i]
    exact (h.backs x).pay i s ((congrFun (h.pins z x) i) ▸ hi)
  · rcases hy:numbering (ℕ⊕ℕ) j with j|j
    · simpa only [t,Edition.from_left _ _ hy,C,balance] using! hd.strong.spends i j
    simpa only [t,Edition.from_right _ _ hy,C,balance,Pi.neg_apply,norm_neg] using! ho.strong.spends i j
  · let S (t:Taste X ζ P R)(f:ℕ×ℕ→ℝ):ℕ×ℕ→ℝ:=fun z=> if i∈(t.menu.marks z.1 z.2).val then Poly.toll w (t.menu.marks z.1 z.2)*P.p.mass (P.activities.forced z.1).support (f z) else 0
    change SumBudget (S C t) _
    rw [show S C t=Sum.elim (S d hd.strong.black) (S o ho.strong.black) ∘ numberX from ?_,add_mul]; swap
    · funext j; unfold S C balance t numberX; cases hi:numbering (ℕ⊕ℕ) j.2 with
      | inl _=> simp [Edition.blend,Function.comp_apply,hi,Prod.map_def,Equiv.prodSumDistrib]
      | inr _=> simp [Edition.blend,Function.comp_apply,hi,Prod.map_def,Equiv.prodSumDistrib]
    exact Cost.equiv _ (Cost.sum (f:=Sum.elim (S d hd.strong.black) (S o ho.strong.black)) (hd.strong.till _) (ho.strong.till _))
  change (C.leaf x).captions.Sound ζ
  rw [hC x]; exact (h.stays x).vertical
end YM.RG3.Script.Picnic
