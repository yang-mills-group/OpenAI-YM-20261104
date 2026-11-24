import YM.FVA2.Weak
import YM.FVA2.OrbitConnection

/-!
# Position cover and quotient lifts in Landau gauge

No asymptotic assumptions. All identities at the even lattice quotient.
At an inversion fixed site in particular the mean weight is NOT the same
as at a two-element orbit. Use total on *cover*, for normalizing scalar fields.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Trans
open Lattice Gauge FormalOPE.RG10 FormalOPE.RG10.BlockGauge
open PertExtension PertExtension.Series PertExtension.Orb PertExtension.Chart
open Function Finset Filter Set Metric MeasureTheory Precision Inherit Push.Loops TreeBasis
open Wilson -- caution Wilson names
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable (G : Gauge) (n : Side)

def coverL : Cone G n →ₗ[ℝ] (Edge (Site n)→ G.Color) := LinearMap.pi (fun i=> if eR i=i then LinearMap.proj (Orb.index i) else -(LinearMap.proj (Orb.index i)))
lemma assemble_exp (x : Cone G n) : Wilson.assemble G n x=expLinks G _ (coverL G n x):= by
  funext e; by_cases h:eR e=e <;> simp [assemble,coverL,liftLinks,expLinks,h, Next.SectorChange.exp_negative]
lemma coverL_at (x:Cone G n) (i:OEdge n) : coverL G n x i.val=x i:= by simp only [coverL, LinearMap.pi_apply, i.property, if_true, LinearMap.proj_apply, show Orb.index i.val=i from Subtype.ext i.property]
-- if_pos works? coe LinearMap ...
lemma coverL_inj : Injective (coverL G n) := fun a b h=> funext (fun i=> by rw [← coverL_at G n a i,← coverL_at G n b i,h])

lemma cover_reflect (hn:_root_.Even n.val)(x:Cone G n) (i:Edge (Site n)) : coverL G n x (Orb.reflect i)= -coverL G n x i:= by
  have he:= no_fixed_edge hn i; unfold coverL; simp only [eR_reflect, show Orb.index (Orb.reflect i)= Orb.index i from Subtype.ext (eR_reflect _), LinearMap.pi_apply ]; rcases eR_spec i with h|h <;> simp only [h, if_neg he, if_neg (Ne.symm he), if_true, LinearMap.neg_apply, neg_neg] -- check
lemma own_image {x : Edge (Site n)→ G.Color}(hx:∀ i,x (Orb.reflect i)= -x i): coverL G n (fun i=>x i.val)=x:= by
  funext i; by_cases he : eR i=i
  · exact (coverL_at G n _ ⟨i,he⟩)
  simp only [coverL, he,↓reduceIte,LinearMap.pi_apply,LinearMap.neg_apply,LinearMap.proj_apply,Orb.index]; rw [(eR_spec i).resolve_left he,hx,neg_neg]
lemma treeCover (u:Wilson.Field G n) : coverL G n (enter G (staple n) u)= variation (accountBasis G n u) := by
   have hv (i:OEdge n): enter G (staple n) u i=genJet (accountBasis G n u) i := by
      unfold genJet; rw [enter_v]; unfold Loom.Truss.stitch; by_cases ht:(staple n).Branch i
      · rw [dif_pos ht,dif_neg (not_not.mpr ((same_staple i).mp ht))]; rfl
      rw [dif_neg ht,dif_pos ((same_staple i).not.mp ht)]; exact (accountPoint u ⟨i,ht⟩).symm
   funext i; change _=if eR i=i then _ else _; by_cases ht:eR i=i
   · rw [if_pos ht]; simp [coverL,ht,hv]
   rw [if_neg ht]; simp only [coverL, LinearMap.pi_apply, if_neg ht,LinearMap.neg_apply,LinearMap.proj_apply,hv]

abbrev GColor (p:Edge (Site n)→G.Color) (a:G.ColorIndex) : Green.ArrayA n := fun i x=> p (x,i) a
abbrev Colour (p:Cone G n)(a:G.ColorIndex) := GColor G n (coverL G n p) a
lemma curry_colour (p:Cone G n)(q:Face (Per n))(a:G.ColorIndex): Curl (coverL G n p) q.1 q.2.val.1 q.2.val.2 a = Green.curl (Colour G n p a) q.2.val.1 q.2.val.2 q.1:= by unfold Green.curl Curl; rw [Pi.sub_apply, Green.fwd_of, Green.fwd_of]; simp only [PiLp.add_apply,PiLp.sub_apply]; unfold Colour GColor; abel

abbrev GSite (n : Side) := Vertex n
abbrev Param (G : Gauge) (n:Side) := Root (rim n) G
def siteCopy : (GSite n → G.Color) →ₗ[ℝ] (Site n→G.Color):= LinearMap.pi fun i => LinearMap.proj (track i)
def averageG : (GSite n→G.Color) →ₗ[ℝ] G.Color := MS.Orbit.νt n • (∑ x: Site n, LinearMap.proj (track x))

def meanZero : Param G n →ₗ[ℝ] (GSite n→G.Color) := LinearMap.pi fun i=>
         (LinearMap.proj i - averageG G n).comp (guarded G (rim n))

def siteCover := siteCopy G n ∘ₗ meanZero G n
lemma average_at (p: GSite n→G.Color): averageG G n p= MS.Orbit.νt n • ∑ i: Site n,p (track i):= by simp [averageG,LinearMap.sum_apply]
lemma ν_card : (Fintype.card (Site n):ℝ)* MS.Orbit.νt n=1:= by simp [MS.Orbit.νt]
lemma average_const (k:G.Color): averageG G n (fun _=>k)=k:= by rw [average_at,Finset.sum_const,card_univ,← Nat.cast_smul_eq_nsmul ℝ, smul_smul,mul_comm,ν_card,one_smul]
lemma zero_mean (p:Param G n): averageG G n (meanZero G n p)=0 := by rw [show meanZero G n p= guarded G (rim n) p-fun _=> averageG G n (guarded G (rim n) p) from rfl, map_sub,average_const, sub_self]
lemma evenSite (p: Param G n) (x:Site n): siteCover G n p (-x)=siteCover G n p x := by simp [siteCover,siteCopy]
lemma sum_mean (p:Param G n): ∑ x:Site n,siteCover G n p x=0:= by have h:=zero_mean G n p; rw [average_at] at h; exact (smul_eq_zero.mp h).resolve_left (MS.Orbit.ν_pos n|>.ne')
lemma to_full {f: Site n→G.Color} (h:∀ x,f (-x)=f x) : siteCopy G n (fun i=> f i.val)=f := by
  funext i; change f (vertex i)=_; rcases vertex_spec i with hx|hx <;> rw [hx]; exact h i
lemma in_sector {f : Site n → G.Color}(h:∀ x,f (-x)=f x)(ht:∑ x:Site n,f x=0): ∃ p, siteCover G n p=f:= by
   let d (i:GSite n):=f i.val; have he : siteCopy G n d=f:=to_full G n h; let z:=d (rim n).origin; let p:Param G n:=fun i=>d i.val-z
   have hz:guarded G (rim n) p=d-(fun _=>z):= by
      funext i; by_cases h:i=(rim n).origin; · subst i; rw [guard_zero]; change 0=z-z; rw [sub_self]
      exact guard_off G (rim n) p ⟨i,h⟩
   have hv: averageG G n d=0:= by rw [average_at]; rw [← he] at ht; rw [show ∑ i : Site n,d (track i)=0 from ht, smul_zero]
   refine ⟨p,?_⟩; rw [siteCover, LinearMap.comp_apply, show meanZero G n p= d from ?_, he]
   funext i; change guarded G (rim n) p i-averageG G n _= d i; rw [hz,map_sub, average_const,hv]; rw [Pi.sub_apply]; abel
lemma differential (p:Param G n): ∀ i:Edge (Site n),coverL G n (d G (rim n) p) i = siteCover G n p (i.1+step i.2) - siteCover G n p i.1 := by
   let g:= fun (i:Edge (Site n))=> siteCover G n p (i.1+step i.2) - siteCover G n p i.1
   have he i:g (Orb.reflect i)= -g i:= by unfold g; dsimp only [Orb.reflect]; rw [sub_add_cancel,show -i.1-step i.2= -(i.1+step i.2) from (by abel), evenSite,evenSite]; abel
   have hm : d G (rim n) p= fun i=>g i.val:= by funext i; rw [TreeBasis.diff]; let t:= guarded G (rim n) p; let s:= t (track (i.val.1+step i.val.2)); let r:=t (track i.val.1); let P:= averageG G n t; change s-r=(s-P)-(r-P); abel
   exact fun i=> by change _=g i; rw [hm,own_image G n he]
lemma grad_color (p:Param G n)(a:G.ColorIndex): Colour G n (d G (rim n) p) a= Green.grad (fun i=>siteCover G n p i a):= by funext i x; unfold Colour GColor; rw [differential]; rfl
end YM.FVA2.Trans
