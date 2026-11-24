import YM.Integration.WilsonOriginalJointDeckMotion
import YM.Push.LOCAL_SPLITTING.Transport

/-! A deck translation of the original paid walk moves every active endpoint, its word and its front together. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalLocatedDeckAction
open Function Finset Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Sunrise Stationary Push Source Labels Next.Foundations
open Further.PhysicalPeriodLimitF933 Macrame Shingle FVA1Physical FVA1Physical.TwoReset
open WilsonOriginalPaidWalkCover WilsonOriginalConnectedPeriodPage WilsonOriginalJointDeckMotion WilsonEmittedRootedJetWage
open scoped Classical BigOperators
variable {G:Gauge} {n N:Side} {V X:Type} [DecidableEq V] {o:Passport n V} {J:Census V}

def step (h:n.val∣N.val) (x:Site n) (a:Deck h) (p:Fin (Pages n N)):Fin (Pages n N):=
  (page h x).symm ⟨a.val+(page h x p).val,by
    apply (Shingle.posted _ _ _).mpr
    rw [map_add,show splitter h a.val=0 from a.property,below,zero_add]⟩

theorem value (h:n.val∣N.val) (x:Site n) (a:Deck h) (p:Fin (Pages n N)):
    (page h x (step h x a p)).val=a.val+(page h x p).val:=
  congrArg Subtype.val ((page h x).apply_symm_apply _)

def steps (h:n.val∣N.val) (x:Site n) (a:Deck h):Fin (Pages n N)≃Fin (Pages n N) where
  toFun:=step h x a
  invFun:=step h x (-a)
  left_inv p:=by apply (page h x).injective;apply Subtype.ext;rw [value,value];simp
  right_inv p:=by apply (page h x).injective;apply Subtype.ext;rw [value,value];simp

theorem sites (h:n.val∣N.val) (A:Row o J G X) (p:Fin (Pages n N)) (a:Deck h) (v:V) (hv:v∈A.mode.val):
    site h A (step h A.center a p) v=a.val+site h A p v:=by
  rw [←travel h A _ v hv,←travel h A p v hv]
  unfold anchor
  rw [value,Work.E03.stop_add_left]

theorem roots (h:n.val∣N.val) (A:Row o J G X) (p:Fin (Pages n N)) (a:Deck h) (v:V) (hv:v∈A.mode.val):
    index h A (step h A.center a p) v=step h (o.origin v) a (index h A p v):=by
  apply (page h _).injective
  apply Subtype.ext
  rw [value,active_page,active_page,sites h A p a v hv]

theorem held (a:Site N) (z:Joint G N):
    RG.increment 1 (motion G a z).2=translate (-a) (RG.increment 1 z.2):=by
  funext e
  have changeAt (B:Link G N):edgeColor (WilsonOriginalLinkedAngularPage.move G a B) e=edgeColor B (e.1-a,e.2):=rfl
  change G.lieExp (edgeColor (WilsonOriginalLinkedAngularPage.move G a (edgeColor.symm z.2)) e)*1=G.lieExp (z.2 (e.1+-a,e.2))*1
  rw [changeAt,ContinuousLinearEquiv.apply_symm_apply,sub_eq_add_neg]

theorem marked (h:n.val∣N.val) (A:Row o J G X) (p:Fin (Pages n N)) (a:Deck h) (z:Joint G N):
    let y:=row h A (step h A.center a p)
    let x:=row h A p
    Loan.letter y.lamp y.atom y.center (motion G a.val z).1 (RG.increment 1 (motion G a.val z).2)=
      Loan.letter x.lamp x.atom x.center z.1 (RG.increment 1 z.2):=by
  intro y x
  subst y;subst x
  rw [centered,centered,held]
  change z.1^A.lamp.stamp*A.atom.unmasked (translate (-a.val) (RG.increment 1 z.2)) (page h A.center (step h A.center a p)).val=
      z.1^A.lamp.stamp*A.atom.unmasked (RG.increment 1 z.2) (page h A.center p).val
  rw [value]
  simp only [Atom.unmasked,Slot.atSite,Push.Local.expand_translate,add_comm a.val (page h A.center p).val,add_neg_cancel_right]

end YM.Integration.WilsonOriginalLocatedDeckAction
