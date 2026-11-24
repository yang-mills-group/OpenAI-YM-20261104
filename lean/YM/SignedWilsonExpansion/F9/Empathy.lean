import YM.SignedWilsonExpansion.F9.PaceB
/-!
# Scalar, finite-dimensional and contour charge utilities on seats Poly
-/
set_option autoImplicit false
noncomputable section
namespace YM.SignedWilsonExpansion.Commission
open WilsonCoeffUV.Bank Function Filter Set
open scoped BigOperators Topology ContDiff Classical
variable {ι σ σ' η θ:Type*}
variable {l:Filter ι}{q:ι→ℝ}
-- real and complex neutral
variable {E F V R:Type*} [NormedField R]
variable [AddCommGroup E][Module R E] [AddCommGroup F][Module R F] [AddCommGroup V][Module R V]
variable (l q)
abbrev Across (R:Type*)[NormedField R][Module R E](f:ι→ E): Prop:= ∀ L: Module.Dual R E, Billed l q (fun i=>L (f i))
variable {l q} (h:Maxer l q)
namespace Across
variable {x y:ι→E}
lemma arrow (p:Across l q R x)(L:E→ₗ[R] F): Across l q R (L ∘ x):=fun Q=> p (Q ∘ₗ L)
lemma solid (t:E) : Across l q R (fun _=>t):= fun i=> Billed.const _
lemma via (p:Across l q R x)(v:x=ᶠ[l] y): Across l q R y:=fun i=> (p i).via (v.fun_comp i).symm
lemma scalar (p:Across l q R x)(f:E→ₗ[R]R): Billed l q (fun i=> f (x i)):= p f
include h
lemma acrossN (p:Across l q R x) : Across l q R (fun i=> -x i):=by intro i; simp_rw [map_neg]; exact ( BoundPoly.grow (p i) (Eventually.of_forall fun j=>le_of_eq (norm_neg ..)))
lemma acrossAdd (p: Across l q R x)(v:Across l q R y):Across l q R (fun i=> x i+y i):= fun i=> by simp_rw [map_add]; exact Billed.add h (p i) (v i)
lemma acrossSub (p:Across l q R x)(v:Across l q R y): Across l q R (fun i=>x i-y i):= fun i=> by simp_rw [map_sub]; exact Billed.diff h (p i) (v i)
lemma sum (P:ι→σ→E)(S:Finset σ)(v:∀ i∈ S,Across l q R (fun j=>P j i)): Across l q R (fun i=>∑ j∈ S,P i j):=by intro i; simp_rw [map_sum]; exact Billed.sum h (fun s j=>i (P j s)) S (fun a p=> v a p i)
lemma smul (f:ι→R)(p:Billed l q f)(v:Across l q R x): Across l q R (fun i=> f i • x i):= fun i=>by simp_rw [map_smul]; exact Billed.smul h _ _ p (v i)
lemma asBasis [Fintype σ](B:Module.Basis σ R E)(x:ι→ E) (p:∀ j,Billed l q (fun i=> B.repr (x i) j)): Across l q R x:=
   via (sum h (fun i (j:σ)=> B.repr (x i) j • B j ) Finset.univ (fun i _=> smul h _ (p i) (solid _))) (Eventually.of_forall fun i=> B.sum_repr _)
lemma basisN [Fintype σ](B:Module.Basis σ R E)(x:ι→E)(p:Billed l q (fun i=>B.equivFun (x i))): Across l q R x:=asBasis h B x fun j=> BoundPoly.grow p (Eventually.of_forall fun i=> norm_le_pi_norm _ j) -- name `p.grow` wants BoundPoly
lemma acrossP [Fintype σ](B:Module.Basis σ R E)(p:Across l q R x): Billed l q (fun i=>B.equivFun (x i)):= Billed.pi h _ (fun i=> p (B.coord i))
lemma column [FiniteDimensional R E] {A:ι→ E→ₗ[R] F} (v:∀ z:E,Across l q R (fun j=> A j z))(x:ι→ E)(p:Across l q R x): Across l q R (fun i=> A i (x i)):=by
    let B:=Module.finBasis R E; conv => arg 4; ext i; rw [←B.sum_repr (x i),map_sum]
    simp_rw [map_smul]; exact sum h _ _ fun i _=> smul h _ (p (B.coord i)) (v (B i))
lemma atBasis [Fintype η](B:Module.Basis η R E)(A:ι→ E→ₗ[R]F)(u:∀t, Across l q R (fun i=>A i (B t)))(p:E): Across l q R (fun i=> A i p):=by
    rw [← B.sum_repr p]; simp_rw [map_sum,map_smul]; exact sum h _ _ fun i _=> smul h _ (Billed.const _) (u i)
lemma actEnough [Fintype η](B:Module.Basis η R E)(P:ι→ E→ₗ[R] V)(u:∀ i:η,Across l q R (fun v=> P v (B i))): Across l q R P:=by
    let vP(i:η)(x:V): E→ₗ[R]V:=(B.coord i).smulRight x; let L(i:η): V→ₗ[R] (E→ₗ[R] V):={ toFun:= vP i, map_add':= by intro x y; ext1 z; exact smul_add .., map_smul':= fun c x=> LinearMap.ext (fun z=>smul_comm ..) }
    have hp(i):Across l q R (fun x=>vP i (P x (B i))):= (u i).arrow (L i)
    apply (sum h (fun x i=>vP i (P x (B i))) Finset.univ (fun i _=>hp i)).via; refine Eventually.of_forall (fun i=>?_); apply B.ext; intro j; rw [LinearMap.sum_apply,Finset.sum_eq_single j]; · simp [vP];
    · intro i _ p; simp [vP,p,Ne.symm p]
    simp
lemma linearAt [FiniteDimensional R E] {P:ι→ E→ₗ[R]F}(p:Across l q R P)(v:Across l q R x): Across l q R (fun i=> P i (x i)):= column h (fun i=> p.arrow (LinearMap.applyₗ (R:=R) i)) x v -- name
omit h
lemma scalar_id {x:ι→R}(p:Across l q R x): Billed l q x:= p LinearMap.id
include h
lemma to_scal {x:ι→R}(p:Billed l q x): Across l q R x:= (smul h _ p (solid (1:R))).via (Eventually.of_forall fun i=>mul_one _)
end Across
lemma Billed.ofRealB {f:ι→ℝ} (p:Billed l q (f : ι→ ℝ)): Billed l q (fun i=> (f i:ℂ)):= BoundPoly.grow p (Eventually.of_forall fun i=> le_of_eq (Complex.norm_real _)) -- need implicit
lemma Billed.reC {f:ι→ℂ}(p:Billed l q f): Billed l q (fun i=> (f i).re):= BoundPoly.grow p (Eventually.of_forall fun i=> Complex.abs_re_le_norm _)
lemma Billed.star {f:ι→ℂ}(p:Billed l q f): Billed l q (fun i=> star (f i)):= BoundPoly.grow p (Eventually.of_forall fun i=> le_of_eq (norm_star _))
section transfer
variable [Module ℂ E][Module ℝ E][ IsScalarTower ℝ ℂ E ] -- omit R from params? types E
variable [FiniteDimensional ℝ E]
include h
lemma Across.realComplex {P:ι→ E}(p:Across l q ℝ P): Across l q ℂ P:=by
   intro i
   let B:=Module.finBasis ℝ E; have he(v:ι): i (P v)=∑ j,( B.repr (P v) j) • i (B j):=by nth_rw 1 [←B.sum_repr (P v)]; rw [map_sum]; exact Finset.sum_congr rfl fun _ _=> map_smul (i.restrictScalars ℝ) _ _
   apply Billed.via ( Billed.sum h (fun j v=>B.repr (P v) j • i (B j)) _ (fun j _=> Billed.smul h _ _ (p (B.coord j)) (Billed.const _))); exact Eventually.of_forall he
end transfer
end YM.SignedWilsonExpansion.Commission
