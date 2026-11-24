import YM.MS.Color.Only
import YangMills.WilsonProof.NativeSupport.YM.Extra.WEAK_SCALING_ACTLAW.Color
/-!
# Scalarization of invariant alternating color tensors
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Only
open Gauge Set Filter LinearMap
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius
variable {G : Gauge}
section alternating
variable (B : Tri G ℝ) (he : ∀ x y z, B x y z= -B y x z) (hs : ∀ x y z,B x y z=B y z x)
def fromB : G.Color →ₗ[ℝ] Module.End ℝ G.Color  where
   toFun x:= (hook G).comp (B x)
   map_add' x y:= by ext1 z; simp
   map_smul' c x:= by ext1 z; simp
lemma pairing (x y z) : ⟪fromB B x y,z⟫_ℝ=B x y z:= hop ..
local notation "D" => fromB B
include he
lemma derivation (hs : ∀ x y z,B x y z=B y z x)
    (hi : ∀ i x y z, B (G.ad i x) y z + B x (G.ad i y) z + B x y (G.ad i z)=0) (x y) : D x * G.ad y - G.ad y *D x= G.ad (D x y) := by
   -- B(x,[y,z],w)=⟨[D_x y,z]+[y,D_x z], w⟩ =⟨D_x y,[z,w]⟩-⟨D_x z,[y,w]⟩
   apply LinearMap.ext; intro z; apply ext_inner_right ℝ; intro w
   simp only [Module.End.mul_apply,LinearMap.sub_apply,inner_sub_left,pairing]
   rw [Gauge.ad_skew,pairing,rotate, real_inner_comm (D x y), pairing]; -- linear equations from invariance;
   -- abbreviate unknown B([x,y],z,w) ...
   have hcy u v i j := hs (G.ad u v) i j
   have hy i a b c:= hi i a b c
   have h1:= hy x y z w; have h2:=hy y x z w; have h3:=hy z x y w; have h4:= hy w x y z; -- rewrite via anti etc with explicit chosen orientation
   set Uxy:= B (G.ad x y) z w; set Uxz:= B (G.ad x z) y w; set Uxw:= B (G.ad x w) y z; set Uyz:=B (G.ad y z) x w; set Uyw:=B (G.ad y w) x z; set Uzw:=B (G.ad z w) x y
   -- invariance x: Uxy-Uxz+Uxw=0
   have a1 : Uxy-Uxz+Uxw=0:= by unfold Uxy Uxz Uxw; rw [he y,← hs (G.ad x w)] at h1; linarith
   have a2 : -Uxy-Uyz+Uyw=0:= by unfold Uxy Uyz Uyw; rw [ad_anti y x,map_neg,LinearMap.neg_apply,LinearMap.neg_apply,he x,← hs (G.ad y w)] at h2; linarith
   have a3 : -Uxz+Uyz+Uzw=0:= by unfold Uxz Uyz Uzw; rw [he x,ad_anti z x,ad_anti z y,map_neg,map_neg,LinearMap.neg_apply,LinearMap.neg_apply,LinearMap.neg_apply,LinearMap.neg_apply, neg_neg,← hs (G.ad z w)] at h3; linarith
   have a4 : -Uxw+Uyw-Uzw=0:= by unfold Uxw Uyw Uzw; rw [he x,← hs (G.ad w z),ad_anti w x,ad_anti w y,ad_anti w z,map_neg,map_neg,map_neg,LinearMap.neg_apply,LinearMap.neg_apply,LinearMap.neg_apply,LinearMap.neg_apply,LinearMap.neg_apply,LinearMap.neg_apply] at h4; linarith
   rw [he x (G.ad y z),← hs (G.ad y w),← hs (G.ad z w)] -- goal B x y [z,w] good; want (-Uyz)+Uyw-Uzw=0 ⇒ h2? h2=-Uxy+ -Uyz+Uyw=0 ; Uzw = Uxy. derive
   change -Uyz- -Uyw=Uzw
   linarith
end alternating
namespace Triple
open Extra.WeakScaling.Color
variable {B : Tri G ℝ}
private theorem calib {E V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E] (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] V)
    {f g h:ℝ→E} {x y z:E} (hf:HasDerivAt f x 0) (hg:HasDerivAt g y 0) (hh:HasDerivAt h z 0):
    HasDerivAt (fun u=> T (f u) (g u) (h u)) (T x (g 0) (h 0) + T (f 0) y (h 0) + T (f 0) (g 0) z) 0 := by
      have H0 : HasFDerivAt T T (f 0) := T.hasFDerivAt
      have he := HasFDerivAt.comp_hasDerivAt (0:ℝ) (E:= E →L[ℝ] E →L[ℝ] V) (l':=T) (l:=(T:E → _)) H0 hf
      have hv := HasDerivAt.clm_apply he hg
      have hz := HasDerivAt.clm_apply hv hh
      simpa only [Function.comp_apply, _root_.add_apply] using hz

theorem reg (B : Tri G ℝ) (h : ∀ g x y z,B (G.adjoint g x) (G.adjoint g y) (G.adjoint g z)=B x y z) (i x y z : G.Color): B (G.ad i x) y z+B x (G.ad i y) z+B x y (G.ad i z)=0:= by
    let V := LinearMap.toContinuousLinearMap (𝕜:=ℝ) (E:=G.Color) (F':=ℝ)
    let T : G.Color→L[ℝ] G.Color→L[ℝ] G.Color→L[ℝ] ℝ := ((LinearMap.toContinuousLinearMap.toLinearMap).comp (B.compr₂ V.toLinearMap)).toContinuousLinearMap -- B.compr₂ V uses right codomain? yep
    let A (t:ℝ) (x:G.Color) := G.adjoint (G.lieExp (t • i)) x
    have h' : HasDerivAt (fun t=> T (A t x) (A t y) (A t z)) ( T (G.ad i x) (A 0 y) (A 0 z)+T (A 0 x) (G.ad i y) (A 0 z)+T (A 0 x) (A 0 y) (G.ad i z)) 0 := calib T (tangent i x) (tangent i y) (tangent i z)
    have hv (x:G.Color): G.adjoint (G.lieExp ((0:ℝ) • i)) x=x:= G.colorMat_injective (by simp)
    have he x y z : T x y z=B x y z:= rfl
    unfold A at h'; simp_rw [he,h,hv] at h'; exact h'.unique (hasDerivAt_const ..)

theorem constant (B : Tri G ℝ) (H : G.Simple) (he : ∀ x y z, B x y z= - B y x z) (hs : ∀ x y z,B x y z=B y z x) (hi : ∀ g x y z, B (G.adjoint g x) (G.adjoint g y) (G.adjoint g z)= B x y z) : ∃ c:ℝ, ∀ x y z, B x y z = c*⟪G.ad x y,z⟫_ℝ:= by
   let D:= fromB B
   choose v hv using (fun (x:G.Color)=> traceTest H (D x) (derivation B he hs (reg B hi) x))
   have ha x : D x= G.ad (v x):= hv x
   let L : G.Color →ₗ[ℝ] G.Color := {
      toFun:=v
      map_add' x y:= ideals_z H (by rw [map_add, ← ha,← ha,← ha,map_add])
      map_smul' t x:= ideals_z H (by rw [map_smul, ← ha,← ha,map_smul]; rfl) }
   have hm x : D x=G.ad (L x):= ha x
   have hw i x : G.ad i*D x - D x*G.ad i= D (G.ad i x):= by
       apply LinearMap.ext; intro y; apply ext_inner_right ℝ; intro z
       have hL:=reg B hi i x y z
       simp only [Module.End.mul_apply, LinearMap.sub_apply,D,inner_sub_left,Gauge.ad_skew,pairing]; linarith only [hL]
   have hp i x : L (G.ad i x)=G.ad i (L x) := ideals_z H (by rw [Gauge.ad_jacobi,← hm,← hm]; exact (hw i x).symm)
   -- turn equivariance into symmetry of ⟪Lx,y⟫ uses compatibility ad: [Lx,y]=[x,Ly] (by equivariance), Killing trace
   let A : Bi G ℝ:= LinearMap.mk₂ ℝ (fun x y=> ⟪L x,y⟫_ℝ) (fun _ _ _=>by rw [map_add, inner_add_left]) (fun _ _ _=>by rw [map_smul, real_inner_smul_left, smul_eq_mul]) (fun _ _ _=> inner_add_right ..) (fun _ _ _=> by rw [real_inner_smul_right, smul_eq_mul])
   have hA i x y : A (G.ad i x) y= -A x (G.ad i y):= by change inner ℝ (L _) _ = _; rw [hp]; exact Gauge.ad_skew ..
   have heq (x y:G.Color): A x y=A y x:= by
      apply sub_eq_zero.mp; refine Extra.WeakScaling.Color.ad_skew H (A-A.flip) (fun _ _=> by simp) (fun i x y=> ?_) x y
      simp only [LinearMap.sub_apply,flip_apply]; rw [hA, hA i y]; abel -- orientation issue
   obtain ⟨c,hc⟩:= invariant_scalar H A heq hA; refine ⟨c,fun x y z=>?_⟩; have hk t : L t=c • t:= ext_inner_right ℝ (fun y=> by rw [real_inner_smul_left]; exact hc t y)
   rw [← pairing, show fromB B x = G.ad (L x) from hm x,hk,map_smul,LinearMap.smul_apply,real_inner_smul_left]

def project (p : ℂ→ₗ[ℝ]ℝ) (F: Tri G ℂ) : Tri G ℝ := F.compr₂ ((LinearMap.llcomp ℝ G.Color ℂ ℝ) p) -- check
lemma complex (F : Tri G ℂ) (H : G.Simple) (he : ∀ i j k,F i j k= - F j i k) (hs : ∀ i j k,F i j k=F j k i) (h : ∀ g x y z, F (G.adjoint g x) (G.adjoint g y) (G.adjoint g z)=F x y z): ∃ c : ℂ, ∀ x y z, F x y z= ⟪G.ad x y,z⟫_ℝ • c:= by
   have h0 (p : ℂ→ₗ[ℝ]ℝ) := constant (project p F) H (fun x y z=> by change p _ = -(p _); exact (congr_arg p (he x y z)).trans (map_neg ..)) (fun x y z=> congr_arg p (hs x y z)) (fun g x y z=> congr_arg p (h g x y z))
   obtain ⟨a,ha⟩:=h0 Complex.reCLM.toLinearMap; obtain ⟨b,hb⟩:=h0 Complex.imCLM.toLinearMap
   refine ⟨⟨a,b⟩,fun i j k=>?_⟩; apply Complex.ext
   · rw [Complex.smul_re,smul_eq_mul,mul_comm]; exact ha i j k
   rw [Complex.smul_im,smul_eq_mul,mul_comm]; exact hb i j k
end Triple
end YM.MS.Only
