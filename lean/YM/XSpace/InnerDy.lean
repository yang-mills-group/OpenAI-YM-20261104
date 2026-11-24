import YM.XSpace.Dyes
import YM.Next.MAXWELL.Simple
/-! # Cartan 3-form uniqueness for MERGE simple colors -/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Stab
open Function Set Filter MeasureTheory Next.Rank Maxwell.Free ProbeLine LinearMap InnerProductSpace OJoint
open scoped Topology BigOperators InnerProductSpace ContDiff Matrix.Norms.Frobenius Classical
variable {G : Gauge} (H:G.Simple)

include H
lemma faithful (x : G.Color)(hx:G.ad x=0): x=0:= by
  have he:= Gauge.trace_adjoint H x x; rw [hx,zero_mul,map_zero, neg_zero,zero_eq_mul] at he; exact inner_self_eq_zero.mp (he.resolve_left (Gauge.casimir_pos H).ne')

lemma inside (Q : Module.End ℝ G.Color)(h : ∀ x y,Q (G.ad x y)=G.ad (Q x) y+G.ad x (Q y)) : ∃ x, Q=G.ad x:= by
  let p:G.Color →ₗ[ℝ] ℝ:= (trace ℝ G.Color).comp ((mulLeft ℝ Q).comp G.ad)
  let V := (toDual ℝ G.Color).symm p.toContinuousLinearMap
  let u:=-G.casimir⁻¹ • V
  let Y:= Q-G.ad u
  have he(x): trace ℝ G.Color (Y*G.ad x)=0 := by
    unfold Y; rw [sub_mul,map_sub,sub_eq_zero];
    rw [← neg_inj, Gauge.trace_adjoint H]; rw [show u=-G.casimir⁻¹ • V from rfl,inner_smul_left, show inner ℝ V x=trace ℝ G.Color (Q*G.ad x) from toDual_symm_apply]; simp [← mul_assoc, (Gauge.casimir_pos H).ne']
  have hb(x y:G.Color) : trace ℝ G.Color (G.ad (Y x)*G.ad y)=0:= by
    have hu(z:G.Color): Q*G.ad z-G.ad z*Q= G.ad (Q z):= by
      apply LinearMap.ext; intro v; change Q (G.ad z v)-G.ad z (Q v)=G.ad (Q z) v; rw [h,add_sub_cancel_right]
    have hs:Y*G.ad x-G.ad x*Y=G.ad (Y x):= by simp only [Y,LinearMap.sub_apply, _root_.map_sub,Gauge.ad_jacobi,sub_mul, mul_sub,← hu]; abel -- ad_jacobi
    rw [← hs]; have hv:=he (G.ad x y); rw [Gauge.ad_jacobi] at hv
    simp only [_root_.mul_sub,_root_.sub_mul,_root_.map_sub] at *; rw [mul_assoc Y,show trace ℝ G.Color (G.ad x*Y*G.ad y)=trace ℝ G.Color (Y*(G.ad y*G.ad x)) from ?_]; exact hv
    rw [mul_assoc (G.ad x), trace_mul_comm ℝ (G.ad x),mul_assoc]

  have hz : Y=0:= by
    apply LinearMap.ext; intro p
    have hx:= hb p (Y p); have hv:=Gauge.trace_adjoint H (Y p) (Y p); rw [hx,neg_zero,zero_eq_mul] at hv; exact inner_self_eq_zero.mp (hv.resolve_left (Gauge.casimir_pos H).ne')
  exact ⟨u,sub_eq_zero.mp hz⟩

omit H
lemma commL (u:G.El)(x:G.Color): G.adjoint u (G.adjoint u⁻¹ x)=x:=by rw [← G.adjoint_mul]; simp
lemma identity_adj (u:G.El)(x y:G.Color): inner ℝ (G.adjoint u x) (G.adjoint u y)=inner ℝ x y := (show G.Color →ₗᵢ[ℝ] G.Color from ⟨G.adjoint u,G.norm_adjoint u⟩).inner_map_map x y
lemma adjoint_ad (u:G.El)(x y:G.Color): G.adjoint u (G.ad x y)=G.ad (G.adjoint u x) (G.adjoint u y):=by apply G.colorMat_injective; simp [show ∀ (x:G.Mat), star (G.mat u)*(G.mat u*x)=x from fun x=> by rw [← mul_assoc]; simp,G.mat_adjoint,G.colorMat_ad,Gauge.conjugate,mul_assoc,sub_mul,mul_sub]

abbrev Triple (G:Gauge):= G.Color→ₗ[ℝ] G.Color→ₗ[ℝ] G.Color→ₗ[ℝ] ℝ

include H
set_option maxHeartbeats 600000 in
lemma alternate (F:Triple G)(hp:∀ x y z,F x y z= - F y x z)(hf:∀ x y z,F x y z= -F x z y)
    (h:∀ u:G.El,∀ x y z,F (G.adjoint u x) (G.adjoint u y) (G.adjoint u z)=F x y z): ∃ c:ℝ,∀ x y z, F x y z= c*inner ℝ (G.ad x y) z:= by
  let A(x:G.Color): Module.End ℝ G.Color:= (toDual ℝ G.Color).symm.toLinearEquiv.toLinearMap.comp (toContinuousLinearMap.toLinearMap.comp (F x))
  have hA(x y z): inner ℝ (A x y) z= F x y z:= toDual_symm_apply
  have hh(x y z w): F (G.ad x y) z w+ F y (G.ad x z) w + F y z (G.ad x w)=0:= by
    let K(b:G.Color) (t:ℝ) := G.adjoint (G.lieExp (t • x)) b
    let V: G.Color→ₗ[ℝ] G.Color →ₗ[ℝ] G.Color:= F.compr₂ ((toDual ℝ G.Color).symm.toLinearEquiv.toLinearMap.comp toContinuousLinearMap.toLinearMap)
    let W:= toContinuousLinearMap (𝕜:=ℝ) (E:=G.Color) (F':= G.Color →L[ℝ] G.Color) (toContinuousLinearMap.toLinearMap ∘ₗ V)
    have he b : HasDerivAt (K b) (G.ad x b) 0:= adj_has ..
    have hb (y): HasDerivAt (fun r=> W (K y r)) (W (G.ad x y)) 0:= W.hasFDerivAt.comp_hasDerivAt 0 (he y)
    have hx : HasDerivAt (fun r=>W (K y r) (K z r)) (W (G.ad x y) (K z 0) + W (K y 0) (G.ad x z)) 0 := (hb y).clm_apply (he z)
    have ht := hx.inner (𝕜:=ℝ) (he w)
    simp only [show ∀ b,K b 0=b from fun b=>by simp [K]] at ht
    rw [show (fun t=>inner ℝ (W (K y t) (K z t)) (K w t)) = fun t:ℝ=>F y z w from funext fun t=> Eq.trans (hA (K y t) (K z t) (K w t)) (h _ _ _ _)] at ht
    have hs:= ht.unique (hasDerivAt_const ..)
    rw [inner_add_left] at hs
    rw [add_comm]; simpa only [show ∀ x y z,inner ℝ (W x y) z= F x y z from hA] using hs
  have hj(x u v w): F x (G.ad u v) w = F x u (G.ad v w)+F x v (G.ad w u):= by
    -- alt closed. RHS? d_beta= beta([u,v],w)+beta([v,w],u)+beta([w,u],v)=0 yes
    have a:= hh x u v w
    have b:=hh u x v w; have c:=hh v x u w; have s:=hh w x u v;
    rw [skew_ad u x, map_neg] at b; rw [skew_ad v u,skew_ad v x] at c; rw [skew_ad w u,skew_ad w v,skew_ad w x] at s; simp only [map_neg,LinearMap.neg_apply] at b c s;
    -- normalize slots
    rw [hp (G.ad x w) u, hf u (G.ad x w),hf x (G.ad u w)] at s
    rw [hp (G.ad x v) u] at c
    rw [skew_ad w u, _root_.map_neg]
    linarith only [a,b,c,s]
  have hs (x u v:G.Color): A x (G.ad u v)= G.ad (A x u) v+G.ad u (A x v):= by
    apply ext_inner_right ℝ; intro w; rw [inner_add_left,skew_ad (A x u), inner_neg_left, Gauge.ad_skew,Gauge.ad_skew]; rw [hA,hA,hA,hj,skew_ad w u,_root_.map_neg]; abel
  choose T hT using fun x=>inside H (A x) (hs x)
  have hi : Injective G.ad:= LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr (fun a => faithful H a)) -- guess
  let L:Module.End ℝ G.Color:= {
    toFun x:=T x
    map_add' x y:= by apply hi; rw [_root_.map_add, ← hT, ← hT, ← hT]; apply LinearMap.ext; intro z; apply ext_inner_right ℝ; intro v; rw [LinearMap.add_apply, inner_add_left,hA,hA,hA,map_add];rfl
    map_smul' t y:= by apply hi; change _= G.ad (t • T y); rw [_root_.map_smul, ← hT,← hT]; apply LinearMap.ext; intro z; apply ext_inner_right ℝ; intro v; rw [LinearMap.smul_apply, real_inner_smul_left,hA,hA,_root_.map_smul];rfl }
  have hg x y z : F x y z=inner ℝ (G.ad (L x) y) z:= by change _= inner ℝ (G.ad (T x) y) _; rw [← hT,hA]
  have hl(g:G.El)(x y z): inner ℝ (G.ad (L (G.adjoint g x)) (G.adjoint g y)) (G.adjoint g z)=inner ℝ (G.ad (G.adjoint g (L x)) (G.adjoint g y)) (G.adjoint g z):= by rw [← hg,h, hg,← adjoint_ad,identity_adj]
  have hw(g:G.El)(x): L (G.adjoint g x)=G.adjoint g (L x):= by
    apply hi; apply LinearMap.ext; intro y; apply ext_inner_right ℝ; intro z; rw [← commL g y,← commL g z]; exact hl _ _ _ _
  obtain ⟨c,hc⟩:= invariant_two H _ (fB hw)
  have ht x : L x=c • x:= by apply ext_inner_right ℝ; intro y; rw [inner_smul_left];exact hc x y
  exact ⟨c, fun x y z=> by rw [hg,ht,map_smul,LinearMap.smul_apply,inner_smul_left]; rfl⟩
where fB {L:Module.End ℝ G.Color}(h:∀ g:G.El,∀ x,L (G.adjoint g x)=G.adjoint g (L x)): Maxwell.Free.irreduc₂ ((innerₗ G.Color).comp L):= by intro u x y; change inner ℝ (L (G.adjoint u x)) _=_; rw [h]; exact identity_adj .. -- guessed
end YM.XSpace.Stab
