import YM.OPE.Trunk.Heavy
import YM.OPE.Laying.Keyed
/-! # Permissions BEFORE an internal sign replacement -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Log.Trunk.Rhythm.Store
open Function Filter Finset Lattice RG Wilson Source Extra.Histories Labels Pressure
open Push Marker Local MergeProof Accent Ribbons Menu Overlay ManyCopies Cadet Lecture Muster
open Book Book.Mask PhysicalNext.Repeat.Legato Bandage PhysicalNext.Repeat.Mallow Bid
open Drapery Backup Motion Extra.Multi Next.Rank.Station Cells
open Book.Tariff Playout.Rake
open scoped Topology BigOperators Classical ContDiff
variable {I J Z V : Type}[Fintype I][DecidableEq I][Fintype J][DecidableEq J][Fintype Z][DecidableEq Z][Fintype V][DecidableEq V]{G:Gauge}
    {H l m k b N p T t t' q d:ℕ}{Q: Rhythm I}{C:Family G}
set_option quotPrecheck false
variable {S:Q.Loom}{P:I→ Z→ Prop}{u:∀ i:ℕ,I→Site (C.side i p)}
    (U:Q.Tour C S b H N p u)
variable {W r D}(L:LogPackage C W r D)(h:C.Makes)
namespace Variant
open Pigment Highest Plain
-- sign counterterm options permitted with all post other terms except cluster siblings at same cell. Use only through sign capture
-- map projection
abbrev exchangeShape (I Z J:Type): I ⊕ (Z⊕J)≃ (I⊕Z)⊕J:=(Equiv.sumAssoc I Z J).symm
abbrev spoil (Q:Rhythm I)(t:ℕ)(P:Ward (Names V (Q.TypeAt Z t)))(J:Type)[Fintype J][DecidableEq J]: Ward (Names V (Q.TypeAt (Z⊕ J) t)) := pullback (accreditation (exchangeShape (Q.Panel t) Z J)) (clash (recognize (carried Q Z t)) P)
def film (Q:Rhythm I)(Z J:Type)(t:ℕ) (i:I) : Z⊕J→ Prop:= Sum.elim (fun _=>False) (fun _=>i∉ Q.focus t)

variable (s : Ward (Names V (Q.TypeAt Z t))) (hV:Q.Host t (fun _ _=>False) s)
local notation "X'"=> exchangeShape (Q.Panel t) Z J
local notation "K'"=> carried Q Z t
local notation "Y!"=> (recognize (J:=J) K')
lemma clashing {f : I→Z}{s:Ward (Names V Z)}{x y:V×I} (hh:Drapery.room (clash f s) x y) : Drapery.room s (sweep V f x) (sweep V f y)∧((sweep V f x)=(sweep V f y)→ x=y):=by
   obtain ⟨p,⟨hX,hP⟩,hx,hy⟩:=hh; exact ⟨⟨batch (sweep V f) p,hX,mem_image_of_mem _ hx,mem_image_of_mem _ hy⟩, hP hx hy⟩
lemma turnAbout (J:Type)[Fintype J][DecidableEq J](hV:Q.Host t (fun _ _=>False) s): Q.Host t (film Q Z J t) (spoil Q t s J):=by
   let X:= Q.Panel t; let κ:=carried Q Z t; let Y:= recognize (J:=J) κ; let k: Q.Panel t:=owner Q t
   refine ⟨(Pitch.clashAt Y hV.pitch).group, trial _ _ (crashTrials Y hV.lens), ?_,?_⟩
   · rintro v j i he; have he:= clashing (Drapery.seats.mp he); rcases j with j|j <;> rcases i with i|i
     · exact congr_arg Sum.inl (hV.single v j i he.1)
     · exact (hV.acts (p:=k) (x:=j) (v:=v) he.1).elim -- j=inl extra root, i=inr local⇒left root? room order i,j yes
     · have ht:(False):=hV.acts (p:=k) (x:=i) (v:=v) (by obtain ⟨p,hp,hx,hy⟩:=he.1; exact ⟨p,hp,hy,hx⟩); exact ht.elim
     have ht:v=v:=rfl; have h:= he.2 rfl; change (v, Sum.inr i)=(v,Sum.inr j) at h; exact congr_arg Sum.inr (Sum.inr.inj (Prod.mk.inj h).2)
   rintro v (i|i) j hQ; have he:= clashing (Drapery.seats.mp hQ); exact (hV.acts (v:=v) (p:=j) (x:=i) he.1).elim
   intro x hx h'; have ht: x ∈ Q.focus t:=h'; have hh : j=k := Q.swap ((Q.on_focus).1 ht) |> (fun h=> (Q.valent j).symm.trans ((Q.seats ..).2 (Q.conj ((Q.arrives ..).1 hx) h)))
   have he:= clashing (Drapery.seats.mp hQ); subst j; have hz:= he.2 rfl; cases hz
end Variant
end YM.OPE.Log.Trunk.Rhythm.Store
