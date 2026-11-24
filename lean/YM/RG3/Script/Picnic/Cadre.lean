import YM.RG3.Script.Picnic.Stamina
/-!
 # Common labelled analytic or constituent supplies
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Script.Picnic
open Function Lattice RG Wilson Marker Overlay RG3.Forms RG3.Press RG3.Held RG3.Ink
  Extra.Multi Ac Push.AbsoluteSums MeasureTheory Push.Corrected Finset
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {n : Side}{V : Type*}[DecidableEq V]{R:Census V}{ζ : V→Site n}{G : Gauge}
  {X : Type*} {P : Rep G n}(T : X→ Edition ζ R G)

structure Firm : Prop where
  home x y : (T x).home=(T y).home
  pins x y : (T x).pins=(T y).pins
  tag x y : (T x).footer.tag=(T y).footer.tag
  cover x y : (T x).footer.cover=(T y).footer.cover

structure Voucher (p:BudgetPoint)(w:V→ℝ)(a u v Y:ℝ)(f g:ℕ→ℝ) : Prop extends Firm T where
  stays x : (T x).Principle p
  backs x : (T x).Grant p w a u v Y f
  fiscal i : 0≤g i ∧ ∀ x,‖(T x).footer.value i‖≤g i
  ticket x i : SumBudget (per p.B a w (T x).footer.tag (T x).footer.cover g i) Y

namespace Voucher
variable {T}{p:BudgetPoint}{w:V→ℝ}{a u v Y:ℝ}{f g : ℕ→ℝ}(h:Voucher T p w a u v Y f g)
include h
lemma ease {a':ℝ}(hw:∀ s,0<w s)(ha:a'≤a): Voucher T p w a' u v Y f g := by
  refine ⟨h.toFirm,h.stays,fun x=>⟨(h.backs x).one,(h.backs x).nn,(h.backs x).pay, label_budget hw (h.backs x).nn ha (h.backs x).more, label_budget hw (fun _=>norm_nonneg _) ha (h.backs x).captions⟩,h.fiscal,fun x=>?_⟩
  exact label_budget hw (fun i=>(h.fiscal i).1) ha (h.ticket x)

lemma into {U:X→Edition ζ R G}{u' v' Y':ℝ}{f' g':ℕ→ℝ}(hw:∀i,0<w i)
    (he:Voucher U p w a u' v' Y' f' g'): Voucher (fun x=>(T x).add (U x)) p w a (u+u') (v+v') (Y+Y') (Edition.blend f f') (Edition.blend g g'):=by
  refine ⟨?_,fun x=>Edition.principle_plus (h.stays x) (he.stays x),fun x=>Edition.grant_plus hw (h.backs x) (he.backs x),fun i=> ?_,fun x i=>?_⟩
  · exact ⟨fun x y=>congrArg₂ Edition.blend (h.home x y) (he.home x y),fun x y=>congrArg₂ Edition.blend (h.pins x y) (he.pins x y),fun x y=>congrArg₂ Edition.blend (h.tag x y) (he.tag x y),fun x y=>congrArg₂ Edition.blend (h.cover x y) (he.cover x y)⟩
  · cases hs:Extra.Iteration.numbering (ℕ⊕ℕ) i with
    | inl i=> simpa only [Edition.add,Edition.from_left _ _ hs] using h.fiscal i
    | inr i=> simpa only [Edition.add,Edition.from_right _ _ hs] using he.fiscal i
  convert Edition.budget_blend (h.ticket x i) (he.ticket x i) using 1
  ext1 j; cases hs:Extra.Iteration.numbering (ℕ⊕ℕ) j <;> simp only [Edition.add,per,Edition.blend,comp_apply,hs,Sum.elim_inl,Sum.elim_inr]
end Voucher

variable {T}(d : Taste X ζ P R)
variable [Nonempty X]

def endorse (T:X→ Edition ζ R G): Taste X ζ P R:= {
    d with
      menu:= {d.menu with
        «global» x:=(T x).pure
        regular x:=(T x).song
        branch:=(T (Classical.arbitrary X)).home
        rays:=(T (Classical.arbitrary X)).pins}
      tag:=(T (Classical.arbitrary X)).footer.tag
      site:=(T (Classical.arbitrary X)).footer.cover
      score x:=(T x).footer.value
      root:=d.root }

lemma endorsed_eq (h:Firm T) (x:X): (endorse d T).leaf x=(T x).scribe (d.leaf x):=by
  let M:=Classical.arbitrary X
  change (⟨⟨d.menu.origins,(T x).pure,(T M).home,(T M).pins,(T x).song,d.menu.marks,d.menu.force x⟩,⟨_,_,_⟩⟩ : Deck R P)=_
  rw [h.home M x,h.pins M x,d.root]
  congr; exact h.tag M x; exact h.cover M x

lemma menu_store {a u c Y : ℝ}{f g : ℕ→ℝ}{w:V→ℝ}(h:Voucher T P.p w a u c Y f g)(hw:∀s,0<w s)(ha:P.p.supportExponent ≤ a) : Nonempty ((endorse d T).Store w u c Y):=by
  let t:=endorse d T
  let z:= Classical.arbitrary X
  have he := h.ease hw ha
  have hz x : t.leaf x = _:= endorsed_eq d h.toFirm x
  refine ⟨fun x=>?_, hw,fun x=>(h.backs x).one,f,fun i=>?_,(he.backs z).more,
    fun x=> ⟨(h.stays z).vertical.card,(h.stays z).vertical.pins⟩ ,g,h.fiscal,(he.ticket z)⟩ -- sound def casts; field proof
  · change Article.Contents (t.leaf _).contents; rw [hz x]; exact Edition.principle (h.stays x)
  refine ⟨(h.backs z).nn i,fun x i' hh=>?_⟩
  have H := congrFun (h.pins z x) i
  change i' ∈((T z).pins i).val at hh
  rw [show t.menu.branch i=(T x).home i from congrFun (h.home z x) i]
  exact (h.backs x).pay i _ (H ▸ hh)

 omit [Nonempty X] in
lemma grants {w:V→ℝ}{u c γ b a:ℝ}(h:d.Snacks w u c γ b a):
    Voucher (fun x=> Edition.read P (d.leaf x) ζ) P.p w P.p.supportExponent u c a h.strong.white h.gold:=by
  let S x:= Edition.read P (d.leaf x) ζ
  have hs x := d.snack h x
  refine ⟨⟨fun _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl⟩,fun x=>?_, fun x=>?_ ,h.given,fun _=>h.ticket⟩
  · change (S _).Principle _
    have hh: (d.leaf x).Active:=(hs x).1
    refine ⟨hh.articles.proper,fun i j hj=>?_,hh.articles.regular, h.active x⟩
    rw [show ζ j=d.menu.origins j from congrFun d.root.symm _]; exact hh.articles.pins _ _ hj
  refine ⟨(hs x).2.radial.localU,fun i=>(h.strong.bulk i).1,fun i j hj=> (congrFun d.root j) ▸ (h.strong.bulk i).2 x j hj,h.strong.bulkCap,(hs x).2.captions.budget⟩
end YM.RG3.Script.Picnic
