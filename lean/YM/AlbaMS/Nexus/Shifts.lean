import YM.AlbaMS.Nexus.Div
import YM.Push.LOOP_COEFFICIENT.Color
import YM.Gauge.Curvature

/-!
# all chart symmetries of compact gauge color & link inversion

No connected assumption, must certify by actual paths involving an arbitrary g.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Nexus
open Set Function Filter Gauge NormedSpace MeasureTheory Precision LocalH Push.Loops LinearMap
open scoped BigOperators Classical Topology ContDiff Matrix.Norms.Frobenius InnerProductSpace ENNReal Matrix
variable {G : Gauge}{x : G.Color}(p : faces G)(u:G.El)
lemma Quill.trust (h:Quill x): Injective (fderiv ℝ R x):= Function.LeftInverse.injective h.release

-- apt covariance rule checking slots via some matrix automorphism
lemma Quill.via (L : G.Color→L[ℝ]G.Color)(S:G.Mat→L[ℝ]G.Mat)(H : R ∘ L=S ∘ R)(h:Quill x)(he:Quill (L x)) {p q:faces G}
    (H' : str q (R (L x))= S (str p (R x))): arch (L x) q=L (arch x p):=by
  apply he.trust
  rw [he.bless q,H',← h.bless]
  have hh := (G.exp_jet.differentiable (by simp) (L x)).hasFDerivAt.comp x L.hasFDerivAt
  have ht := S.hasFDerivAt.comp x (G.exp_jet.differentiable (by simp) x).hasFDerivAt
  have hu:=DFunLike.congr_fun ((hh.congr_of_eventuallyEq (Filter.Eventually.of_forall (congr_fun H.symm))).unique ht) (arch x p)
  exact hu.symm
lemma Quill.over (h:Quill x)(he:Quill (-x)): arch (-x) (p.2,p.1) = - arch x p:=by
  refine via (L:=-ContinuousLinearMap.id ℝ G.Color) (S:=(starL ℝ:G.Mat≃L[ℝ] G.Mat).toContinuousLinearMap) ?_ h he ?_
  · funext y; change R (-y)=star (R y); exact (congr_arg _ (Work.F03.exp_neg_color y)) -- fix
  change R (-x)*G.colorMat p.1-G.colorMat p.2*R (-x) = star (R x*G.colorMat _-G.colorMat _*R x); simp_rw [R, Work.F03.exp_neg_color,G.mat_inv, star_sub, star_mul, G.colorMat_skew]; simp [sub_eq_add_neg,add_comm]
private lemma on_mat (g h:G.Mat): G.conjugate u (g*h)= G.conjugate u g*G.conjugate u h:= by
  unfold Gauge.conjugate; rw [mul_assoc (G.mat u * g),← mul_assoc (star (G.mat u)),← mul_assoc (star (G.mat u)), G.mat_star_mul,one_mul]; simp [mul_assoc]
lemma Quill.brake (h:Quill x)(he:Quill (G.adjoint u x)): arch (G.adjoint u x) (G.adjoint u p.1, G.adjoint u p.2) = G.adjoint u (arch x p):=by
  have ht v:R (G.adjoint u v) = G.conjugate u (R v):= by rw [R,exp_adjoint]; simp [Gauge.conjugate,R] -- test
  let S:G.Mat→ₗ[ℝ] G.Mat:=(G.conjugateL u).toLinearMap
  apply via (L:=(G.adjoint u).toContinuousLinearMap) (S:=S.toContinuousLinearMap) (funext ht) h he -- elaboration old x
  change R (G.adjoint u x)*G.colorMat (G.adjoint u p.2)-G.colorMat (G.adjoint u p.1)* R (G.adjoint u x) = S (_-_)
  rw [ht, map_sub,G.mat_adjoint,G.mat_adjoint, ← on_mat u,← on_mat u]; rfl
lemma Quill.regain (h:Quill x)(v : G.Color): arch x (v,v)= G.ad x v:=by
  apply h.trust; rw [h.bless]
  let y:=fun t:ℝ=> G.adjoint (G.lieExp (t • -v)) x
  have hh:y 0=x:=by simp [y]
  have ht : HasDerivAt y (G.ad x v) 0 := by
    rw [ad_flip x v]; exact (adjoint_rate (-v) x).congr_deriv (by simp)
  suffices R∘y=(fun t=> G.mat (warp t (v,v) (G.lieExp x))) by
    refine (roll_path (G.lieExp x) (v,v)).unique (this ▸ ?_)
    exact (show HasFDerivAt R (fderiv ℝ R x) (y 0) by rw [hh]; exact (G.exp_jet.differentiable (by simp) x).hasFDerivAt).comp_hasDerivAt 0 ht
  ext1 t; simp only [warp,y, R, Function.comp_apply,exp_adjoint, smul_neg, Work.F03.exp_neg_color,inv_inv]

abbrev W_adj:=printC G (G.adjoint u)
lemma inner_adj (x y : G.Color): ⟪G.adjoint u x,G.adjoint u y⟫_ℝ=⟪x,y⟫_ℝ:= LinearIsometry.inner_map_map (⟨G.adjoint u,G.norm_adjoint u⟩: G.Color→ₗᵢ[ℝ] G.Color) x y
lemma adj_ortho : (W_adj u).transpose*W_adj u=1:= by
  ext i j; simp_rw [Matrix.one_apply,W_adj, printC, Matrix.mul_apply,Matrix.transpose_apply, toMatrix_apply,(base G).coe_toBasis_repr_apply,(base G).repr_apply_apply,(base G).coe_toBasis]; -- sum eq parseval basis
  rw [← orthonormal_iff_ite.mp (base G).orthonormal, ← inner_adj u]; nth_rw 1 [← (base G).sum_inner_mul_inner (G.adjoint u (base G i)) (G.adjoint u (base G j))]
  exact Finset.sum_congr rfl fun k _=>by rw [real_inner_comm (base G k) (G.adjoint u (base G i))]
lemma det_adj : |LinearMap.det (G.adjoint u)|=1:=by
  rw [← det_toMatrix (base G).toBasis]; change |(W_adj u).det|=1 -- hW unused
  have he:= congr_arg Matrix.det (adj_ortho u); rw [Matrix.det_mul,Matrix.det_transpose, Matrix.det_one] at he; rcases sq_eq_one_iff.mp (show (W_adj u).det^2=1 by rw [pow_two,he]) with h|h <;> simp [h] -- fix
lemma Quill.mod (h:Quill x)(he:Quill (G.adjoint u x)): LinearMap.det (M (G.adjoint u x))=LinearMap.det (M x):=by
  have ht : M (G.adjoint u x)* G.adjoint u= G.adjoint u*M x:= by
    ext1 y; change M _ _=G.adjoint u (M x y); simp only [M_ap]; rw [← map_neg]; nth_rw 1 [← map_zero (G.adjoint u)]; exact brake (-y,0) u h he
  have hg:= congr_arg LinearMap.det ht; rw [map_mul,map_mul,mul_comm _ (LinearMap.det (G.adjoint u))] at hg; exact mul_left_cancel₀ (by have hi:=det_adj u; intro hw; rw [hw,abs_zero] at hi; exact zero_ne_one hi) hg
lemma M_rev (h:Quill x)(he:Quill (-x)): M (-x)* G.adjoint (G.lieExp x)⁻¹=M x:=by
  apply LinearMap.ext; intro y; change M _ _=M _ _; simp only [M_ap];
  have ht:= h.over (he:=he) (p:=(-y,0));
  have hh: arch (-x) (0,y)= arch x (-y,0):=by apply neg_injective; rw [← map_neg,← ht]; simp
  rw [← hh]; apply he.trust; rw [he.bless,he.bless]
  change _* G.colorMat 0-G.colorMat (-_)*_= _*G.colorMat _- G.colorMat 0 *_; -- g.inv*y*? 
  simp only [R, Work.F03.exp_neg_color,G.mat_inv,map_neg,G.mat_adjoint,Gauge.conjugate, star_star,map_zero, zero_mul,mul_zero,neg_mul,zero_sub,neg_neg,sub_zero]; rw [mul_assoc (star _* _), G.mat_mul_star,mul_one]
lemma Quill.misty (h:Quill x)(he:Quill (-x)) : Real.log (LinearMap.det (M (-x)))=Real.log (LinearMap.det (M x)):=by
  rw [← M_rev h he,map_mul, ← Real.log_abs (_*_),abs_mul, det_adj, mul_one, Real.log_abs]
end YM.MSBar.Nexus
