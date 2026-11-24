import YM.RegulatorIR.Budget.SpliceCopy
import YM.RegulatorIR.Budget.RayScroll

/-! Consequences for bulk-bulk and source-bulk reduced connections. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Budget
open Function Layer Motion Tuple Packet Deck Copies
open scoped NNReal ENNReal Topology BigOperators Classical
variable {X Y:Type} {P:ℝ} {r s:ℕ} (A:Deck P X Y)

namespace Deck
lemma projectSplit (p:Tuple Y r)(q:Tuple Y s)(w:Tuple X (r+s)) (hw:A.project w=Fin.append p q):
    A.project (cutLeft w) = p ∧ A.project (cutRight w) = q:= by
 refine ⟨funext fun i=>?_, funext fun j=>?_⟩
 · exact (congr_fun hw (Fin.castAdd s i)).trans (Fin.append_left ..)
 exact (congr_fun hw (Fin.natAdd r j)).trans (Fin.append_right ..)

def nestBrace (p:Tuple Y r)(q:Tuple Y s)(i x): Nest A p i x × Stalk A.project q ≃ Nest A (Fin.append p q) (Fin.castAdd s i) x where
 toFun a:=⟨Fin.append a.1.val a.2.val,
   (Tuple.comp_append A.orbit a.1.val a.2.val).trans (congr_arg₂ Fin.append a.1.property.1 a.2.property), (Fin.append_left ..).trans a.1.property.2⟩
 invFun a:=(⟨cutLeft a.val,(projectSplit A p q a.val a.property.1).1,a.property.2⟩,⟨cutRight a.val,(projectSplit A p q a.val a.property.1).2⟩)
 left_inv _:= Prod.ext (Subtype.ext (cutleft ..)) (Subtype.ext (cutright ..))
 right_inv a:=Subtype.ext (recombine a.val)
def stalkBrace (p:Tuple Y r)(q:Tuple Y s): Stalk A.project p × Stalk A.project q ≃ Stalk A.project (Fin.append p q) where
 toFun a:=⟨Fin.append a.1.val a.2.val, (Tuple.comp_append A.orbit a.1.val a.2.val).trans (congr_arg₂ Fin.append a.1.property a.2.property)⟩
 invFun a:= (⟨cutLeft a.val,(projectSplit A p q a.val a.property).1⟩,⟨cutRight a.val,(projectSplit A p q a.val a.property).2⟩)
 left_inv _:= Prod.ext (Subtype.ext (cutleft ..)) (Subtype.ext (cutright ..))
 right_inv a:=Subtype.ext (recombine a.val)
def nestTask (p:Tuple Y r)(i:Fin r)(x:X)(y) : Stalk (fun w:(Nest A p i x) × X=> A.orbit w.2) y ≃ Nest A (Fin.cons y p) i.succ x:=by
 refine Equiv.ofBijective (fun u=> ⟨Fin.cons u.val.2 u.val.1.val,(comp_cons A.orbit ..).trans (congr_arg₂ Fin.cons u.property u.val.1.property.1),?_⟩) ⟨?_,?_⟩
 · change Fin.cons (α:=fun _=>X) u.val.2 u.val.1.val i.succ=x
   rw [Fin.cons_succ]; exact u.val.1.property.2
 · rintro ⟨⟨z,x⟩,hz⟩ ⟨⟨v,y⟩,hv⟩ he
   have H: Fin.cons (α:=fun _=>X) x z.val=Fin.cons y v.val:= Subtype.mk.inj he
   exact Subtype.ext (Prod.ext (Subtype.ext (by have h:=congr_arg (@Fin.tail _ (fun _=>X)) H; simpa using h)) (congr_fun H 0))
 rintro ⟨a,H,hv⟩
 refine ⟨⟨(⟨Fin.tail a,?_,hv⟩,a 0),congr_fun H 0⟩,Subtype.ext (Fin.cons_self_tail ..)⟩
 exact funext fun i=> (congr_fun H i.succ).trans (Fin.cons_succ ..)

def stalkTask (p:Tuple Y r)(y) : Stalk (fun w:(Stalk A.project p) × X=> A.orbit w.2) y ≃ Stalk A.project (Fin.cons y p):=by
 refine Equiv.ofBijective (fun u=> ⟨Fin.cons u.val.2 u.val.1.val,(comp_cons A.orbit ..).trans (congr_arg₂ Fin.cons u.property u.val.1.property)⟩) ⟨?_,?_⟩
 · rintro ⟨⟨z,x⟩,hz⟩ ⟨⟨v,y⟩,hv⟩ he
   have H: Fin.cons (α:=fun _=>X) x z.val=Fin.cons y v.val:= Subtype.mk.inj he
   exact Subtype.ext (Prod.ext (Subtype.ext (by have h:=congr_arg (@Fin.tail _ (fun _=>X)) H; simpa using h)) (congr_fun H 0))
 rintro ⟨a,H⟩
 refine ⟨⟨(⟨Fin.tail a,?_⟩,a 0),congr_fun H 0⟩,Subtype.ext (Fin.cons_self_tail ..)⟩
 exact funext fun i=> (congr_fun H i.succ).trans (Fin.cons_succ ..)
end Deck

section Fold
variable {T:Packet X (r+1)}{U:Packet X (s+1)}{H:Tariff X}{c d:ℝ≥0∞} (hh:A.Ready U) (hu:localQ H U d)(hd:d≠⊤)
include hh hu hd
lemma splice_one_left (h:A.Ready T)(ht:localQ H T c)(hc:c ≠ ⊤)(i:Fin r)(p:Tuple Y r)(q:Tuple Y s) :
   splice (A.deckSum T) (A.deckSum U) (Fin.append p q)= A.deckSum (splice T U) (Fin.append p q):=by
 let x:=A.place (p i); let I:= Nest A p i x
 have he:A.orbit x=p i:= A.placed ..
 let f:I→Tuple X r:= Subtype.val
 have H' (u:Y): A.deckSum T (Fin.cons u p)=Stalk.collect (fun w:I×X=> A.orbit w.2) (zigO A T f) u:= by
    rw [A.deck_pivot h (Fin.cons u p) i.succ x (by rw [Fin.cons_succ]; exact he)]
    exact ((A.nestTask p i x u).tsum_eq (fun z=> A.dyed T z.val)).symm
 have H₁ : quota (zig T f) 1≤c:=by
    let g:I→Hold i x:= fun a=> ⟨a.val,a.property.2⟩
    have hg:Injective g:= fun a b h=> Subtype.ext (Subtype.mk.inj h)
    let G:I×X→Hold i.succ x:= fun a=>Tuple.underL i x (a.2,g a.1)
    have hG:Injective G:= (Tuple.underL i x).injective.comp ((Function.injective_id.prodMap hg).comp ((Equiv.prodComm ..).injective))
    change quota ((T ∘ (Subtype.val : Hold i.succ x→_)) ∘ G) 1≤c
    apply (quota_mono _ (w:=1) (fun i=>H.diameter_unit (G i).val)).trans
    exact (quota_restrict G hG _ (fun z=>H.diameter z.val)).trans (ht ..)
 rw [open_tree A T U q f p hc hd H₁ hu hh H', A.deck_pivot (splice_ready A h hh) (Fin.append p q) (Fin.castAdd s i) x (by rw [Fin.append_left];exact he)]
 exact (nestBrace A p q i x).tsum_eq (fun z=>A.dyed (splice T U) z.val)

def braceRight (p:Tuple Y r)(q:Tuple Y s)(j:Fin s)(m:X) : Stalk A.project p × Nest A q j m ≃ Nest A (Fin.append p q) (Fin.natAdd r j) m where
 toFun a:=⟨Fin.append a.1.val a.2.val,
   (Tuple.comp_append A.orbit a.1.val a.2.val).trans (congr_arg₂ Fin.append a.1.property a.2.property.1), (Fin.append_right ..).trans a.2.property.2⟩
 invFun a:=(⟨cutLeft a.val,(projectSplit A p q a.val a.property.1).1⟩,⟨cutRight a.val,(projectSplit A p q a.val a.property.1).2,a.property.2⟩)
 left_inv _:= Prod.ext (Subtype.ext (cutleft ..)) (Subtype.ext (cutright ..))
 right_inv a:=Subtype.ext (recombine a.val)

lemma splice_projection (h:A.Ready T)(ht:localQ H T c)(hc:c ≠⊤)(v:Tuple Y (r+s))(i:Fin (r+s)) : splice (A.deckSum T) (A.deckSum U) v= A.deckSum (splice T U) v:=by
 obtain ⟨⟨p,q⟩,hp⟩:= (Fin.appendEquiv r s).surjective v; subst v
 induction i using Fin.addCases
 next i=> exact splice_one_left A hh hu hd h ht hc i p q
 next j=>
   change splice (A.deckSum T) (A.deckSum U) (Fin.append p q)= A.deckSum (splice T U) (Fin.append p q)
   rw [twist,splice_one_left A h ht hc hh hu hd j]
   let x:= A.place (q j)
   rw [A.deck_pivot (splice_ready A hh h) (Fin.append q p) (Fin.castAdd r j) x (by rw [Fin.append_left];exact A.placed _),
     A.deck_pivot (splice_ready A h hh) (Fin.append p q) (Fin.natAdd r j) x (by rw [Fin.append_right]; exact A.placed _)]
   unfold lodge
   rw [← (A.nestBrace q p j x).tsum_eq,← ((Equiv.prodComm ..).trans (braceRight A p q j x)).tsum_eq]; apply tsum_congr
   intro i
   change A.dyed (splice U T) (Fin.append i.1.val i.2.val)=A.dyed (splice T U) (Fin.append i.2.val i.1.val)
   unfold dyed; rw [twist,A.attach,A.attach,mul_comm (A.polish i.1.val)]

lemma splice_marked (h:quota T 1 ≠ ⊤) : splice (A.scroll T) (A.deckSum U)= A.scroll (splice T U):=by
 funext v
 obtain ⟨⟨p,q⟩,hp⟩:= (Fin.appendEquiv r s).surjective v; subst v
 change splice _ _ (Fin.append p q)=A.scroll (splice T U) (Fin.append p q)
 let I:=Stalk A.project p; let f:I→Tuple X r:= Subtype.val
 have hr (i:Y): A.scroll T (Fin.cons i p)=Stalk.collect (fun w:I×X=>A.orbit w.2) (zigO A T f) i := ((A.stalkTask p i).tsum_eq (fun v=>A.dyed T v.val)).symm
 have he : quota (zig T f) 1 ≤ quota T 1 := by
    let g:I×X→ Tuple X (r+1):=fun a=> Fin.cons a.2 a.1.val
    have hg:Injective g:= (glueEquiv X r).injective.comp (((Function.injective_id (α:=X)).prodMap Subtype.val_injective).comp ((Equiv.prodComm ..).injective))
    exact quota_restrict g hg T 1
 rw [open_tree A T U q f p h hd he hu hh hr]; exact (A.stalkBrace p q).tsum_eq (fun x=>A.dyed (splice T U) x.val)
end Fold
end YM.RegulatorIR.Budget
