import YM.Euclid.Null
import Mathlib.LinearAlgebra.Dual.Lemmas
/-! # Pick an actual single LINEAR SECTION of the Physical Spectrum at each cap. Preserves true units and reflected & conjugate labels at every admitted position.
 This choice doesn't require weak copies at any head fixed r (connect them on elected filter later). Changing same representative anywhere here costs ZERO in the ordered limit. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.SignedWilsonExpansion.Museum
open Function Filter Set Lattice
open scoped Topology BigOperators Classical
variable {G:Gauge}{L:Register G}{d:ℕ}(S:Table L)(h:S.Basic)(X:S.RealSpin)
local notation "H" => S.Field d -- macro DOT hazard

structure Arm where
  desk : S.Field d →ₗ[ℂ] L.Ref d
  era(x): S.project d (desk x)=x
  dry: desk (S.unit d) = L.scalar d
  spiral(s:Signed)(x): desk (S.mirror X d s x) = L.mirrorGroup d s (desk x)
  adj(x): desk (S.conj X d x) = star (desk x)

include h
lemma sentinel : ∃ l:S.Field d→ₗ[ℂ] L.Ref d,( ∀ x, S.project d (l x)=x) ∧ l (S.unit d)=L.scalar d:=by
   obtain ⟨w,hw⟩:= Module.Projective.exists_dual_eq_one ℂ ( S.alive d h ); let a:=S.representative d; let u:= L.scalar d - a ( S.unit d ); have e:S.project d u=0:=by unfold u; rw [map_sub,show S.project d (a ( S.unit d ))=S.unit d from S.rep ..]; exact sub_self _ -- check
   refine ⟨ a+w.smulRight u,fun x=>?_,?_ ⟩; · simp only [LinearMap.add_apply, map_add, LinearMap.smulRight_apply, a, S.rep]; rw [map_smul,e,smul_zero,add_zero]
   change a _+ w _ • u = _; rw [hw,one_smul]; unfold u; abel

lemma escorted : ∃ l:S.Field d→ₗ[ℂ] L.Ref d,( ∀ x,S.project d (l x)=x ) ∧ l (S.unit d)=L.scalar d ∧ ∀ x, l ( S.conj X d x ) = star ( l x ) :=by
   obtain ⟨u,p,e⟩:= sentinel S (d:=d) h; let v:S.Field d→ₗ[ℂ] L.Ref d:= (L.bar d).comp ( u.comp (S.conj X d) ); have ht(x):v x=star (u (S.conj X d x)):=rfl
   let a:ℂ:=2⁻¹; let l:=a • (u+v); have hv(x):l x=a • ( u x+ star (u ( S.conj X d x )) ):=by simp only [l,LinearMap.smul_apply, LinearMap.add_apply,ht]
   have he(x): S.project d (l x)=x:=by rw [hv,map_smul,map_add,← S.conj_project X,p,p,S.reflect_star]; unfold a; module
   refine ⟨l,he,?_,?_⟩; · rw [hv,S.conj_unit,e,L.bar_scalar]; unfold a; module
   intro x; rw [hv,hv,S.reflect_star,star_smul,star_add,star_star,add_comm]; norm_num [a]

lemma grant : Nonempty ( Arm S (d:=d) X ):=by
   obtain ⟨u,hz,v,w⟩:= escorted S (d:=d) h X
   let c:ℂ:= Fintype.card Signed; let e(b:Signed):= (L.mirrorGroup d b⁻¹).comp (u.comp (S.mirror X d b)); have he(b:Signed)(x):e b x=L.mirrorGroup d b⁻¹ ( u ( S.mirror X d b x ) ):=rfl
   have hm:c≠0:=Nat.cast_ne_zero.mpr (Fintype.card_ne_zero)
   let l:= c⁻¹ • ∑ b:Signed,e b; have u'(x): l x=c⁻¹ • ∑ b:Signed, e b x:=by unfold l; rw [LinearMap.smul_apply,LinearMap.sum_apply]
   have pv (b:Signed)(x): S.project d (e b x)=x:=by rw [he, ←S.mirror_project X,hz, ← S.mirror_mul X, inv_mul_cancel,S.mirror_one]
   have pt (b:Signed): e b (S.unit d)=L.scalar d :=by rw [he,S.mirror_unit,v,L.mirror_scalar]
   refine ⟨l,fun x=>?_,?_,fun b x=>?_,fun x=>?_⟩
   · rw [ u', map_smul, map_sum ]; simp_rw [ pv ]; rw [ Finset.sum_const,Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ,  smul_smul, inv_mul_cancel₀ hm, one_smul ] -- smul_smul? inspect
   · rw [u']; simp_rw [ pt ]; rw [ Finset.sum_const,Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ,  smul_smul, inv_mul_cancel₀ hm, one_smul ]
   · rw [u',u',map_smul,map_sum]; apply congr_arg (fun a=> c⁻¹ • a)
     refine Fintype.sum_equiv (Equiv.mulRight b) _ _ fun a=>?_
     change e a (S.mirror X d b x)=L.mirrorGroup d b ( e (a*b) x ); rw [ he, he, ← S.mirror_mul X, ← L.mirror_mul, mul_inv_rev, ← mul_assoc,mul_inv_cancel,one_mul ] -- expected algebra
   rw [u',u',star_smul,star_sum]
   have hz:star c=c:= by unfold c; simp
   rw [star_inv₀,hz]; apply congr_arg; apply Finset.sum_congr rfl; intro i _; rw [he,he,← S.mirror_star X, w,L.star_mirror]

abbrev Portfolio := ∀ d:ℕ, Arm S (d:=d) X
noncomputable def standT : Portfolio S X:= fun _=> Classical.choice (grant S h X)
end YM.SignedWilsonExpansion.Museum
