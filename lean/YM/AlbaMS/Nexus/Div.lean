import YM.AlbaMS.Nexus.Folio
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.ResolventVolume
import YM.Gauge.Casimir
import YM.LocalH.Haar
/-!
# Divergence

Follow the left-increment vector fields and use the bracket to evaluate under-
determinant derivative. Log-density genuine in any LocalRatio (LocalH.actual
supplies one). No global identification of M as invertible. Does not identify
nonperturbative gauge-fixed measures with limit.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Nexus
open Set Function Filter Gauge NormedSpace MeasureTheory Precision LocalH Push.Loops LinearMap
open scoped BigOperators Classical Topology ContDiff Matrix.Norms.Frobenius InnerProductSpace ENNReal Matrix
variable {G : Gauge}{x : G.Color} {g : G.Mat}

abbrev base (G : Gauge) := EuclideanSpace.basisFun G.ColorIndex ℝ
abbrev printC (G : Gauge) := toMatrix (base G).toBasis (base G).toBasis
-- exp left increment y*R(x)
def M (x:G.Color): G.Color →ₗ[ℝ] G.Color := arch x ∘ₗ ((- (_root_.LinearMap.id (R:=ℝ) (M:=G.Color))).prod (0:G.Color→ₗ[ℝ] G.Color))
abbrev N (x:G.Color) := (fderiv ℝ (fun y=> delta (G.lieExp x) (G.lieExp y)) x).toLinearMap
lemma M_ap (x y : G.Color): M x y= arch x (-y,0):=rfl
lemma Quill.increment (h:Quill x): N x * M x=1:=by
  let f:(G.Color→G.Color):=fun y=> delta (G.lieExp x) (G.lieExp y)
  apply LinearMap.ext; intro w
  let u (t:ℝ):= x+t • (M x w);
  have he : HasDerivAt u (M x w) 0:= by simpa only [id_eq, one_smul] using! ((hasDerivAt_id' (0:ℝ)).smul_const (M x w)).const_add x
  have hz:u 0=x:=by simp [u]
  have ht:fderiv ℝ R x (M x w)=G.colorMat w * R x:=by rw [M_ap, h.bless]; change _* G.colorMat 0-G.colorMat (-w)*_=_; simp
  let v : ℝ → G.El:=fun t=>G.lieExp (u t)
  have hb : HasDerivAt (R∘u) (G.colorMat w * R x) 0:=by
    rw [← ht]; refine HasFDerivAt.comp_hasDerivAt 0 ?_ he; rw [hz]; exact (G.exp_jet.differentiable (by simp) x).hasFDerivAt
  have hh : HasDerivAt (f ∘ u) w 0:= by
    have hu:v 0=G.lieExp x:=by unfold v; rw [hz]
    have hl:=delta_rate (v:=v) (a:=w) (t:=0) (by rw [hu]; exact hb)
    rw [hu] at hl; exact hl
  have hx : ContDiffAt ℝ ω f x:= delta_diff contDiffAt_const G.exp_jet.contDiffAt rfl
  exact ((show HasFDerivAt f (fderiv ℝ f x) (u 0) by rw [hz]; exact (hx.differentiableAt (by simp)).hasFDerivAt).comp_hasDerivAt 0 he).unique hh
lemma Quill.hot (h:Quill x): LinearMap.det (M x)≠0:=by
  intro hn; have he:= congr_arg LinearMap.det h.increment; rw [map_mul,map_one,hn,mul_zero] at he; exact zero_ne_one he
lemma Quill.gigs (h:Quill x){P:ChartRatio G}(hp:LocalRatio P)(he:x∈Metric.ball 0 P.radius):
    P.J x * |LinearMap.det (M x)|=1:=by rw [← exp_delta_det hp he]; change |LinearMap.det (N x)| * |LinearMap.det (M x)|=_; rw [← abs_mul, ← map_mul,h.increment,map_one,abs_one] -- stray
lemma Quill.price (h:Quill x){P:ChartRatio G}(hp:LocalRatio P)(he:x∈Metric.ball 0 P.radius): Real.log (P.J x)= -Real.log (LinearMap.det (M x)):=by
  have ht:= congr_arg Real.log (h.gigs hp he); rw [Real.log_mul (hp.pos _ he).ne' (abs_ne_zero.mpr h.hot), Real.log_abs, Real.log_one] at ht; exact eq_neg_of_add_eq_zero_left ht
lemma decline (x : G.Color): LinearMap.trace ℝ _ (G.ad x)=0:=by
  rw [LinearMap.trace_eq_matrix_trace ℝ (base G).toBasis, Matrix.trace]; apply Finset.sum_eq_zero; intro i _; simp only [Matrix.diag_apply, LinearMap.toMatrix_apply, (base G).coe_toBasis_repr_apply,(base G).repr_apply_apply,(base G).coe_toBasis]; have hh:= G.ad_skew x (base G i) (base G i); rw [real_inner_comm _ (G.ad _ _)] at hh; linarith
-- M moves, trace formula. Adapt ResolventVolume to orientation we have. frame anchored basis.
def stud (P : ChartRatio G)(x:G.Color):= Real.log (P.J x)
lemma lilt {P:ChartRatio G} (hp:LocalRatio P): stud P 0=0:=by rw [stud,hp.anchored,Real.log_one]
lemma Quill.lit {P:ChartRatio G} (hp:LocalRatio P)(x:G.Color)(he:x∈Metric.ball 0 P.radius): ContDiffAt ℝ ω (stud P) x:=(hp.germ x he).log (hp.pos _ he).ne'

lemma Quill.divergence (h:Quill x){P:ChartRatio G}(hp:LocalRatio P)(he:x ∈ Metric.ball 0 P.radius)(p:faces G):
    trace ℝ _ ((fderiv ℝ (fun x=> arch x p) x).toLinearMap) + fderiv ℝ (stud P) x (arch x p)=0:=by
  let u (t:ℝ):= x+t • arch x p; let V:=arch x p; let B:=(fderiv ℝ (fun x=> arch x p) x).toLinearMap
  have hu : HasDerivAt u V 0:=by simpa only [one_smul] using! ((hasDerivAt_id' (0:ℝ)).smul_const V).const_add x
  have hz:u 0=x:=by simp [u];
  let H:= B*M x + M x*G.ad p.1
  have ht (y:G.Color): HasDerivAt (fun t=> M (u t) y) (H y) 0:=by
    have hw : arch x (G.ad p.1 (-y), G.ad p.2 0)=M x (G.ad p.1 y):=by rw [M_ap, map_neg,map_zero]
    have hh:= arch_com h p (-y,0); have hh' : fderiv ℝ (fun x=> arch x (-y,0)) x V-B (M x y)=M x (G.ad p.1 y):=hh.trans hw
    rw [sub_eq_iff_eq_add,add_comm] at hh'; change HasDerivAt ((fun x=> arch x (-y,0)) ∘ u) (B (M x y)+ M x (G.ad p.1 y)) 0; rw [← hh']; refine HasFDerivAt.comp_hasDerivAt _ ?_ hu; rw [hz]; exact ((h.smooth _).differentiableAt (by simp)).hasFDerivAt
  let Q:=printC G; let W:= Q (M x)
  have hW (y): (Q y).det= LinearMap.det y:= LinearMap.det_toMatrix ..; have hh:=h.hot
  have hb : HasDerivAt (fun t=> Real.log (LinearMap.det (M (u t)))) ((W⁻¹ * Q H).trace) 0:=by
    simp_rw [← hW]; unfold W; rw [← hz] -- nth? 
    apply AnalyticNext.ConnectedActivity.ResolventVolume.hasDerivAt_log_det; rw [hz,hW]; exact hh
    intro i j; simp_rw [Q,printC,LinearMap.toMatrix_apply]; exact ((base G).toBasis.coord i).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 (ht ((base G).toBasis j))
  have hw : IsUnit W.det := isUnit_iff_ne_zero.2 (by unfold W; rw [hW]; exact hh)
  have hr : (W⁻¹ * Q H).trace=trace ℝ _ B:=by
    have he (f g): Q (f*g)=(Q f)*(Q g):=LinearMap.toMatrix_mul ..
    have ht : (Q (G.ad p.1)).trace=0:= (trace_eq_matrix_trace ℝ (base G).toBasis (G.ad p.1)).symm.trans (decline p.1)
    unfold H; rw [map_add,he,he,mul_add,← mul_assoc W⁻¹ (Q (M x)), Matrix.nonsing_inv_mul W hw, one_mul,Matrix.trace_add]
    rw [ht,add_zero,← mul_assoc W⁻¹, Matrix.trace_mul_comm, ← mul_assoc, Matrix.mul_nonsing_inv W hw, one_mul]; exact (trace_eq_matrix_trace ℝ (base G).toBasis B).symm
  rw [hr] at hb
  have hd : (fun t=> stud P (u t))=ᶠ[𝓝 0] fun t=> - Real.log (LinearMap.det (M (u t))):=by
    have hl:=hu.continuousAt.tendsto; rw [hz] at hl; filter_upwards [hl.eventually h.again, hl.eventually (Metric.isOpen_ball.mem_nhds he)] with t ht hx; exact ht.price hp hx
  have hg := hb.neg.congr_of_eventuallyEq hd; rw [add_comm]; apply eq_neg_iff_add_eq_zero.mp
  exact ((show HasFDerivAt (stud P) (fderiv ℝ (stud P) x) (u 0) by rw [hz]; exact ((lit hp x he).differentiableAt (by simp)).hasFDerivAt).comp_hasDerivAt 0 hu).unique hg

end YM.MSBar.Nexus
