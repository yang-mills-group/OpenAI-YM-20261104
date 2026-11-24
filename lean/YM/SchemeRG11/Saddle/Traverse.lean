import YM.Pert.Lattice.GaugeFix
import YM.PertExtension.OrbHessian

/-!
# Finite-regulator ORB adaptation

Algebraic splitting of edge coefficients for the ACTUAL inverted, positive-oriented torus,
root gauge independent of torus size/algebra. Needed for Landau and Feynman paths. No
inf-volume or contour arguments.
-/
set_option autoImplicit false
set_option maxHeartbeats 750000
noncomputable section
namespace YM.SchemeRG11.Sway
open scoped Classical
open Function Filter Lattice PertExtension.Orb Pert.Orb
variable {G:Gauge}{n:Side}

abbrev Twig (G:Gauge)(n:Side):= Trees n→ G.Color
abbrev Flow (G:Gauge)(n:Side):= (Mean G n)
abbrev Whole (G:Gauge)(n:Side):= Dir G n × ↥(Flow G n)

def twins : Potential G n →ₗ[ℝ] Dir G n × Twig G n:=
 (LinearMap.pi (fun l:Cotree n=> takeLink l.val.val)).prod (LinearMap.pi (fun l:Trees n=> takeLink l.val.val))
lemma twins_at (a:Potential G n)(l:Cotree n):(twins a).1 l = a.val l.val.val:=rfl
lemma twins_on(a:Potential G n)(l:Trees n):(twins a).2 l=a.val l.val.val:=rfl
lemma twin_inj : Injective (twins (n:=n) (G:=G)):=by
 intro a b he
 have hi(l:OEdge n): a.val l.val=b.val l.val:=by
   by_cases hl:Branch l
   · rw [←twins_on a (⟨l,hl⟩:Trees n),←twins_on b (⟨l,hl⟩:Trees n),he]
   rw [←twins_at a (⟨l,hl⟩:Cotree n),←twins_at b (⟨l,hl⟩:Cotree n),he]
 apply Subtype.ext; funext l
 have ht: a.val (eR l) = b.val (eR l):= hi (index l)
 rcases eR_spec l with h|h
 · rwa [h] at ht
 rw [h] at ht; change a.val (Pert.Orb.image l)= b.val (Pert.Orb.image l) at ht
 rw [a.property,b.property] at ht; exact neg_injective ht

def Gown (v:Dir G n × Twig G n) (e:Pert.Orb.Links n): G.Color:=
 let L(l: OEdge n):= if h:Branch l then v.2 ⟨l,h⟩ else v.1 ⟨l,h⟩
 if eR e=e then L (index e) else -L (index e)
lemma twin_surj (hn:Even n.val): Surjective (twins (n:=n) (G:=G)):=by
 intro v
 have hv : Gown v ∈ LinkP G n:=by
   intro l; change Gown v (reflect l)= - Gown v l
   simp only [Gown, eR_reflect]
   have he : (index (reflect l))=index l:=Subtype.ext (eR_reflect l)
   rw [he]; rcases eR_spec l with h|h
   · rw [h,if_neg (Ne.symm (no_fixed_edge hn l)),if_pos rfl]
   rw [h,if_pos rfl,if_neg (no_fixed_edge hn l),neg_neg]
 refine ⟨⟨Gown v,hv⟩,Prod.ext ?_ ?_⟩
 · funext l; rw [twins_at]; change Gown v l.val.val=_
   simp only [Gown]; rw [if_pos l.val.property,show index l.val.val=l.val from Subtype.ext l.val.property,dif_neg l.property]
 funext l; rw [twins_on]; change Gown v l.val.val=_; simp only [Gown]
 rw [if_pos l.val.property,show index l.val.val=l.val from Subtype.ext l.val.property,dif_pos l.property]

def twin (hn:Even n.val) : Potential G n ≃L[ℝ] Dir G n × Twig G n:=
 (LinearEquiv.ofBijective twins ⟨twin_inj,twin_surj hn⟩).toContinuousLinearEquiv
lemma twin_apply (hn:Even n.val)(a:Potential G n):twin hn a=twins a:=rfl
lemma twin_twists(hn:Even n.val)(A:Dir G n):
   ((twin hn).symm (A,(0:Twig G n))).val= variation A:=by
 let a : Potential G n:= ⟨variation A, variation_invert hn A⟩
 apply congrArg (fun z:Potential G n=>z.val) (show _=a from (twin hn).symm_apply_eq.mpr ?_)
 apply Prod.ext
 · change A=(twin hn a).1
   exact funext fun i=>(variation_others A i).symm
 change (0:Twig G n)=(twin hn a).2
 exact funext fun i=>(variation_branch A i).symm

def struts : Parameter G n →ₗ[ℝ] Twig G n := LinearMap.snd ℝ (Dir G n) (Twig G n) ∘ₗ twins ∘ₗ gZ
lemma struts_apply (z:Parameter G n)(l: Trees n):struts z l= Pert.Orb.grad z.val l.val.val:=rfl
lemma struts_surj(hn:Even n.val): Surjective (struts (G:=G) (n:=n)):=by
 intro v
 let b (l:Trees n) : Multiplicative G.Color := Multiplicative.ofAdd (-(v l))
 let f (u: Site n) := Multiplicative.toAdd (frame b u)
 let p : Parameter G n:=⟨f, ⟨fun x=>congrArg Multiplicative.toAdd (frame_neg b x),by change f 0=0; unfold f; rw [frame,dif_pos (vertex_zero)];rfl⟩⟩
 refine ⟨p,funext fun l=>?_⟩
 have hh:=tree_zero hn b (1:Cotree n→Multiplicative G.Color) l
 let i:= l.val.val
 let x:= i.1; let y:= x+step i.2
 simp only [aligned, links, Lattice.gauge] at hh; rw [lift_at _ l.val,splitLink,dif_pos l.property] at hh
 have he: ((frame b x) * b l)*(frame b y)⁻¹=1:=hh
 have he: (f x + -(v l)) + -(f y) = 0:= congrArg Multiplicative.toAdd he
 change f x - f y = v l
 rw [← sub_eq_zero]
 refine (?_: _ = _) |>.trans he
 abel
lemma struts_zero{p:Parameter G n}(he:struts p=0): p=0:=by
 have h(x:Site n)(hx:x≠0): p.val x=p.val (x+(move x).vec):=by
    let l:=(move x).used x
    let i:Trees n:=⟨picked x,x,hx,rfl⟩
    have hh: (gZ p).val (eR l)=0:=congrFun he i
    have ha: Pert.Orb.grad p.val l=0:=by
      rcases eR_spec l with h|h
      · rw [h] at hh; exact hh
      rw [h] at hh; change (gZ p).val (Pert.Orb.image l)=0 at hh
      rw [(gZ p).property] at hh; exact neg_eq_zero.mp hh
    have hg:=sub_eq_zero.mp ha -- a val l.1 ...
    change p.val l.1=p.val (l.1+step l.2) at hg; unfold l at hg; cases H : move x with
    | mk j c=> rw [H] at hg; cases c
               · exact hg
               simpa [Step.vec,Step.used,sub_eq_add_neg,add_assoc] using hg.symm
 apply Subtype.ext; funext x; change p.val x=0
 induction hz : depth x using Nat.strong_induction_on generalizing x with
 | _ k ih=>by_cases hx:x=0
           · rw [hx];exact atZ p
           rw [h x hx]; exact ih _ (by rw [← hz];exact move_falls hx) _ rfl
lemma struts_inj: Injective (struts (G:=G) (n:=n)):= fun a b h=> sub_eq_zero.mp (struts_zero (by rw [map_sub,h,sub_self]))

def stem (hn:Even n.val): Parameter G n ≃L[ℝ] Twig G n:= (LinearEquiv.ofBijective struts ⟨struts_inj,struts_surj hn⟩).toContinuousLinearEquiv
abbrev spanLink(G:Gauge)(n:Side): Parameter G n≃L[ℝ] ↥(Flow G n):=(bridgeEquiv G n).toContinuousLinearEquiv
abbrev crest (G:Gauge) (hn:Even n.val): ↥(Flow G n)≃L[ℝ] Twig G n:= (spanLink G n).symm.trans (stem hn)
abbrev combine (G:Gauge) (hn:Even n.val): Whole G n≃L[ℝ] Dir G n × Twig G n:= (ContinuousLinearEquiv.refl ℝ _).prodCongr (crest G hn)
abbrev packing (G:Gauge)(hn:Even n.val): Whole G n≃L[ℝ] Potential G n:= (combine G hn).trans (twin hn).symm

end YM.SchemeRG11.Sway
