import YangMills.WilsonProof.NativeSupport.YM.MS.Arc.Forest
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
/-!
# Analytic-weight dimension-radius estimates

Use positive ray only. The program first projects 2m extra directions of external
 vectors and momenta, integrating at that dimension, then differentiates m+1 times,
 then integrates the one **remaining** ray with this weighting, including later signs.
 This order is valid as DimReg (TeX uses either order). Elementary Cost and Majorant
 not a holom TV assumption. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Arc
open Function Filter Set Finset MeasureTheory Real
open scoped Topology ContDiff Interval
open ContinuousLinearMap
variable {I E F G: Type}[NormedAddCommGroup E][NormedSpace ℝ E]
 [NormedAddCommGroup F][NormedSpace ℂ F][NormedSpace ℝ F][IsScalarTower ℝ ℂ F]
 [NormedAddCommGroup G] [NormedSpace ℝ G]
-- weighted argument
abbrev μhalf: Measure ℝ:= volume.restrict (Ioi 0)
def cloud (z:ℂ)(y:ℝ): ℂ:= (y:ℂ) ^ (2*z+1)
lemma cloud_weight {z:ℂ}{y:ℝ}(hy:0<y): ‖cloud z y‖= y ^ (2*z.re+1):= by rw [cloud, Complex.norm_cpow_eq_rpow_re_of_pos hy]; simp
lemma cloud_near {b:ℕ}{z:ℂ} (hz:0<2*z.re+1)(hp:2*z.re+1≤(b:ℝ)){y:ℝ}(hy:0<y) : ‖cloud z y‖≤(1+‖y‖)^b:= by
   rw [cloud_weight hy,norm_of_nonneg hy.le]; refine le_trans (b:= (1+y) ^ (2*z.re+1)) ?_ ?_; · gcongr; simp
   rw [← rpow_natCast]; gcongr; linarith
lemma cloud_sees {z:ℂ} : AEStronglyMeasurable (cloud z) μhalf:= by
   refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi; intro y hy; exact ((Complex.continuous_ofReal.continuousAt).cpow (g:=fun _=> 2*z+1) continuousAt_const (Complex.ofReal_mem_slitPlane.mpr hy)).continuousWithinAt -- inspect
-- canonical density estimates. `shadeB w a b` uses generic weight V_i.
variable {z:UScale I}{a V: I→ℝ}{u:I→ Tree E F}{w:I→ℝ→ℂ}{b:ℕ}
structure shadeB (w:I→ℝ→ℂ)(v:I→ℝ)(m:ℕ): Prop where
    borel i : AEStronglyMeasurable (w i) μhalf
    pay i: ∀ᵐ p ∂μhalf, ‖w i p‖ ≤ v i * (1+‖p‖)^m
    pos i: 0≤v i
lemma shade_cloud {Z:I→ℂ}(hz:∀ i,0<2*(Z i).re+1)(ht:∀ i,2*(Z i).re+1≤(b:ℝ)) : shadeB (fun i=>cloud (Z i)) 1 b:= ⟨fun _=>cloud_sees,fun i=> (ae_restrict_mem measurableSet_Ioi).mono fun t ht'=> by simpa using cloud_near (hz i) (ht i) ht',fun _=>zero_le_one⟩
-- density Pw=vertex
variable (h:quiet z u a)(hw:shadeB w V b)
def fetchP (w:ℝ→ℂ) (f:Tree E F)(p:ℝ)(x:E): F:= w p • f (p,x)
private def dust : ℝ→ℝ := fun p=> ((1+‖p‖)^2)⁻¹
private lemma dust_pays : Integrable dust μhalf:= by
   have h:= Reserve.dustInteg (S:=path fun x:Unit=>0) (i:=Unit.unit) (E:=ℝ) (μ:=volume) 2 (by simp); have hh : (path (fun x:Unit=> (0:ℝ))).dust 2 () = dust:= funext fun p:ℝ => by simp [Scale.dust,dust,Scale.weight]
   rw [hh] at h; exact h.restrict
include h
lemma slice_fit (p:ℝ)(q:E)(j:ℕ)(i:I): iteratedFDeriv ℝ j (fetchP (w i) (u i) p) q= w i p • iteratedFDeriv ℝ j (fun q=>u i (p,q)) q:= by
    let Z:E→ℝ×E := fun x=>(p,x); exact iteratedFDeriv_const_smul_apply' ( ((h.smooth i).comp (show ContDiff ℝ ∞ Z by unfold Z; fun_prop)).contDiffAt.of_le (by exact_mod_cast le_top))
include hw
lemma shade_price (j:ℕ): ∃ C:ℝ,0<C∧∃ k:ℕ,∀ i, ∀ᵐ t ∂μhalf,∀ x, ‖iteratedFDeriv ℝ j (fetchP (w i) (u i) t) x‖ ≤ C*((1+|z i|)*(1+‖x‖))^k*(a i*V i)*dust t := by
    obtain ⟨C,hC,k,hk⟩:= Q.man h j (b+2); refine ⟨C,hC,k,fun i=>?_⟩; filter_upwards [hw.pay i] with t ht; intro x; rw [slice_fit h, norm_smul];
    have hp (w:ℕ): 0 < (1+‖t‖)^w:= pow_pos (by positivity) _; have hx:= hw.pos i; let X:= C*((1+|z i|)*(1+‖x‖))^k
    have hh := norm_extDer (h.smooth i) t x j; have hm := hk i (t,x).1 x; have he : (X*a i / (1+‖t‖)^(b+2))*V i*(1+‖t‖)^b ≤ X*(a i*V i)*dust t:= by apply le_of_eq; unfold dust; rw [pow_add]; field_simp
    refine le_trans (mul_le_mul ht (hh.trans ((le_div_iff₀ (hp (b+2))).mpr (hk i t x))) (norm_nonneg _) (mul_nonneg hx (hp b).le)) (le_trans ?_ he); unfold X; exact Eq.le (by ring)
lemma shade_major (i:I) : Majorant μhalf (fetchP (w i) (u i)) where
   smooth:= (Eventually.of_forall (fun p=> (((h.smooth i).comp (show ContDiff ℝ ∞ (fun x:E=> (p,x)) by fun_prop))).const_smul (w i p))) -- `IsScalarTower` ContinuousConstSMul
   borel j x:= by simp_rw [slice_fit h]; exact (hw.borel i).smul (((h.major (Reserve.cover (μ:=volume) 2 (by simp)) i).borel j x).restrict)
   major j x:= by
       obtain ⟨C,hC,k,hk⟩:= shade_price h hw j; let L:= C*((1+|z i|)*(1+(‖x‖+1)))^k*(a i*V i); refine ⟨Metric.ball 0 (‖x‖+1), Metric.isOpen_ball.mem_nhds (by simp),fun x=> L*dust x,dust_pays.const_mul L,(hk i).mono fun t ht p hp=>?_⟩; apply (ht p).trans; have ht:= Q.nonneg h i; have hx:= hw.pos i; have he : 0<dust t:= inv_pos.mpr (by positivity); unfold L; dsimp only; gcongr; exact le_of_lt (by simpa using hp)
variable [CompleteSpace F]
def fetching (f: Tree E F)(Z:ℝ→ℂ): E→F:= fun x=> ∫ t, fetchP Z f t x ∂μhalf
lemma shade_fin : veg z (fun i=> fetching (u i) (w i)) (fun i=> a i* V i):= by
   apply hike (fun i=> (shade_major h hw i).contDiff); intro j; obtain ⟨C,hC,k,hk⟩:= shade_price h hw j
   let D:= max (∫ x,dust x ∂μhalf) 1; refine ⟨C*D, mul_pos hC (lt_max_of_lt_right zero_lt_one),k,fun i p=>?_⟩
   let K:=C*((1+|z i|)*(1+‖p‖))^k*(a i*V i); have hz:=Q.nonneg h i; have he:=hw.pos i; have hp : 0 ≤ K:= by unfold K; positivity
   rw [(shade_major h hw i).identity]; refine le_trans (norm_integral_le_of_norm_le (dust_pays.const_mul K) ((hk i).mono fun t ht=> ht p)) ?_; rw [integral_const_mul]; refine le_trans (mul_le_mul_of_nonneg_left (le_max_left _ 1) hp) ?_; unfold K D; exact Eq.le (by ring)
end YM.MS.Arc
