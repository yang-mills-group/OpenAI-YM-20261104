import YM.AlbaMS.Nexus.Div
import YM.AlbaMS.Loft.Grove
import YM.Push.LOOP_COEFFICIENT.Color

/-!
# Incidence versions. Works still for based gauge

Keep chosen link & site type `V`, `I`. Evolutions in native units first (unit
vol, independent ghost & L & K). Does not require orientation even quotient
assumption! Useful when transferring quotient to based gauge for exact tests.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Inlay
open Set Function Filter Gauge NormedSpace MeasureTheory Precision LocalH Push.Loops LinearMap
open scoped BigOperators Classical Topology ContDiff Matrix.Norms.Frobenius InnerProductSpace ENNReal Matrix
open Nexus Loft Loft.Chart Bric Coil
variable {G : Gauge} {V I R : Type*}
abbrev ink (G:Gauge)(V : Type*):= V→ G.Color
abbrev Flit (G:Gauge)(V:Type*):= V × G.ColorIndex
abbrev Leaf (G:Gauge)(V I :Type*):= Place (Flit G V) (Flit G I)
abbrev Heave (G:Gauge)(V I R :Type*)[CommRing R]:= Floor (Flit G V) (Flit G I) R
structure Net (V I:Type*) where
   head : V→Option I
   foot : V→ Option I

def slabQ (i:Flit G V): ink G V:= Pi.single i.1 (base G i.2)
def coefQ (v:G.ColorIndex) : G.Color →ₗ[ℝ] ℝ := (base G).toBasis.coord v
def stip (i:Flit G V) : ink G V→ₗ[ℝ] ℝ:= coefQ i.2 ∘ₗ LinearMap.proj i.1
lemma stip_at (i:Flit G V)(q : ink G V): stip i q=coefQ i.2 (q i.1):= rfl
lemma coef_at (i:G.ColorIndex)(q:G.Color): coefQ i q= (base G).toBasis.repr q i:=rfl
lemma coef_inner (i:G.ColorIndex)(q:G.Color): coefQ i q=⟪base G i,q⟫_ℝ:=by rw [coef_at,(base G).coe_toBasis_repr_apply,(base G).repr_apply_apply]
lemma slab (i:V)(α:G.ColorIndex)(x:V): slabQ (i,α) x=if x=i then base G α else 0:=by rw [slabQ,Pi.single_apply]
lemma coef_base (i j:G.ColorIndex): coefQ i (base G j)= if j=i then 1 else 0:=by rw [coef_inner,orthonormal_iff_ite.mp (base G).orthonormal]; by_cases h:i=j<;>simp [h,eq_comm]
lemma c_split (v:G.Color): (∑ j:G.ColorIndex,coefQ j v • base G j)=v:=(base G).toBasis.sum_repr v
lemma stip_slab (i j:Flit G V): stip i (slabQ j)= if j=i then 1 else 0:=by
  rw [stip_at]; cases i with|mk i u=> cases j with |mk j v=>
   simp_rw [slab _ v, apply_ite (coefQ (G:=G) u),map_zero,coef_base]; by_cases h:j=i; · simp [h]
   simp [h,Ne.symm h]

-- ghosts, with pulled base; gauge type finite only when doing total transforms
abbrev pads (i:Option I): ink G I →ₗ[ℝ] G.Color := i.elim 0 (fun j=> LinearMap.proj j)
def cbron (x y:G.ColorIndex)(z:G.ColorIndex):= coefQ z (G.ad (base G x) (base G y))
lemma b_flip (x y z:G.ColorIndex):cbron x y z = -cbron y x z:=by rw [cbron,ad_flip,map_neg,cbron]
lemma b_tr (x y:G.ColorIndex): cbron x y y=0:=by
  rw [cbron,coef_inner]; have hh:= G.ad_skew (base G x) (base G y) (base G y); rw [real_inner_comm (G.ad _ _)] at hh; rw [real_inner_comm]; linarith

def adI (x y : ink G I): ink G I:= fun i=> G.ad (x i) (y i)
lemma cJac (x y z w:G.ColorIndex): (∑ i:G.ColorIndex,cbron x y i*cbron i z w)+ (∑ i:G.ColorIndex,cbron y z i*cbron i x w)+(∑ i:G.ColorIndex,cbron z x i*cbron i y w)=0:=by
  have ht (x y z:G.ColorIndex): ∑ i:G.ColorIndex,cbron x y i*cbron i z w= coefQ w (G.ad (G.ad (base G x) (base G y)) (base G z)):=by
    rw [← c_split (G.ad (base G x) (base G y))]; simp_rw [map_sum,LinearMap.sum_apply, map_smul, LinearMap.smul_apply,map_sum,map_smul]; rfl -- fix
  simp_rw [ht,← map_add];
  let X:=base G x; let Y:=base G y; let Z:=base G z
  have hp : G.ad (G.ad X Y) Z+G.ad (G.ad Y Z) X+G.ad (G.ad Z X) Y=0:=by rw [G.ad_jacobi, LinearMap.sub_apply, Module.End.mul_apply,Module.End.mul_apply, ad_flip (G.ad Y Z), ad_flip Z, map_neg, LinearMap.neg_apply, ad_flip (G.ad X Z)]; abel
  change coefQ w (_:_)=0; rw [hp,map_zero]
variable [Fintype V] [Fintype I]
lemma slab_total (x:ink G V): (∑ i:Flit G V, stip i x • slabQ i)=x:=by
  rw [Fintype.sum_prod_type]; ext1 i; rw [Finset.sum_apply, Finset.sum_eq_single i]; simp_rw [Finset.sum_apply]; convert c_split (x i) using 1; apply Finset.sum_congr rfl; intro j _; change stip (i,j) x • slabQ (i,j) i=_; rw [slab i j i,if_pos rfl]; rfl; intro j _ hj; rw [Finset.sum_apply]; apply Finset.sum_eq_zero; intro u _; change  stip (j,u) x • (slabQ (G:=G) (j,u) i)=0; rw [slab,if_neg (Ne.symm hj),smul_zero]; simp

def grit (G:Gauge)(I:Type*)[Fintype I]: Codes (Flit G I) ℝ where
 price i j k:=if i.1=k.1 ∧ j.1=k.1 then cbron i.2 j.2 k.2 else 0
 skew i j k:= by by_cases h:i.1=k.1<;> by_cases ht:j.1=k.1<;> simp only [h,ht,and_true,and_false,↓reduceIte,neg_zero]; exact b_flip ..
 Jac x y z i:=by
   have he (x y z : Flit G I) : (∑ j:Flit G I, (ite (x.1=j.1 ∧ y.1=j.1) (cbron x.2 y.2 j.2) 0)*(ite (j.1=i.1 ∧ z.1=i.1) (cbron j.2 z.2 i.2) 0))=if x.1=i.1 ∧ y.1=i.1∧ z.1=i.1 then ∑ j:G.ColorIndex,cbron x.2 y.2 j*cbron j z.2 i.2 else 0:=by rw [Fintype.sum_prod_type, Finset.sum_eq_single i.1]; by_cases h:x.1=i.1<;> by_cases ht:y.1=i.1 <;> by_cases hu:z.1=i.1<;> simp [h,ht,hu]; intro j _ hj; simp [hj]; simp -- sequencing issue
   rw [he,he,he]; by_cases h:x.1=i.1<;> by_cases ht:y.1=i.1<;> by_cases hh:z.1=i.1<;>simp [h,ht,hh,cJac]
 tr x y:=by simp_rw [b_tr]; simp
lemma grit_price (x y z:Flit G I): (grit G I).price x y z=stip z (adI (slabQ x) (slabQ y)):=by
  change ite _ _ _=coefQ z.2 (G.ad _ _); cases x; cases y; rename_i i x j y; by_cases ht:i=z.1 <;> by_cases h:j=z.1 <;> simp [ht,h,Ne.symm,slab,cbron,base] -- goal tail
end YM.MSBar.Inlay
