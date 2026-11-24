import YM.OPE.Compatible.Glim.Caps
import YM.Next.STATIONARY.Joint.OnShell
/-! # Jacobian derivative ∞ -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Variance
open Function Filter Set MeasureTheory Lattice Wilson RG Precision Metric Matrix Cascade ContinuousLinearMap
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{P:ChartRatio G}
attribute [local instance] Gauge.frobInner
open Next.SectorChange Stationary
variable {E F I:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
-- for any chart motion.The upper derivative Dσ computed from full product
noncomputable abbrev sway (h:ℝ×E→F)(t:ℝ×E):= fderiv ℝ h t (1,0)
lemma Arch (F:ℝ×E→F) {t:ℝ}{x:E}(h:ContDiffAt ℝ ω F (t,x)):
    ContDiffAt ℝ ω (sway F) (t,x):= ContDiffAt.clm_apply (g:=fun _=>(1,0)) (h.fderiv_right (by simp)) contDiffAt_const
lemma sky (f:ℝ×E→F) {x:E}(hf:ContDiffAt ℝ ω f (0,x)):
     HasDerivAt (fun t=> f (t,x)) (sway f (0,x)) 0:=by
        have ht:HasDerivAt (fun t:ℝ=>(t,x)) (1,0) (0:ℝ):= (hasDerivAt_id' (0:ℝ)).prodMk (hasDerivAt_const (0:ℝ) x); exact (hf.differentiableAt (by simp)|>.hasFDerivAt).comp_hasDerivAt 0 ht
lemma sideways (f:ℝ×E→F) {x:E}(hf:ContDiffAt ℝ ω f (0,x))(z:E):
     HasDerivAt (fun t:ℝ=> fderiv ℝ (fun y=> f (t,y)) x z) (fderiv ℝ (fun y=> sway f (0,y)) x z) 0:=by
        let V(t:ℝ):= (t,x); have ht:HasDerivAt V (1,0) 0:=(hasDerivAt_id' (0:ℝ)).prodMk (hasDerivAt_const (0:ℝ) x)
        let H:=fderiv ℝ f; let u:=((0:ℝ),x); have hp:DifferentiableAt ℝ H u:= (hf.fderiv_right (m:=ω) (by simp)).differentiableAt (by simp)
        let Q:= ContinuousLinearMap.apply ℝ F ((0:ℝ),z); let S:= ContinuousLinearMap.apply ℝ F ((1:ℝ),(0:E)); have he:∀ᶠ i:ℝ in 𝓝 0,fderiv ℝ (fun y=> f (i,y)) x z= Q (H (i,x)):=by
             filter_upwards [ht.continuousAt.tendsto.eventually (hf.eventually (by simp))] with i hi; let A:=fun y:E=> (i,y); have hi':HasFDerivAt A (ContinuousLinearMap.inr ℝ ℝ E) x:=(hasFDerivAt_const _ _).prodMk (hasFDerivAt_id x); exact congr_arg (fun f:E→L[ℝ]F=>f z) ((((show ContDiffAt ℝ ω f (A x) from hi).differentiableAt (by simp)).hasFDerivAt.comp _ hi').fderiv)
        have hs: fderiv ℝ (fun y=> sway f (0,y)) x z=Q (fderiv ℝ H u (1,0)):=by
             let g:= ContinuousLinearMap.inr ℝ ℝ E; have he: (fun y=> sway f (0,y))= (S ∘ H ∘ g):=rfl; erw [he,fderiv_comp x S.differentiableAt (hp.comp x g.differentiableAt),fderiv_comp x hp g.differentiableAt,g.fderiv,S.fderiv]; exact (hf.isSymmSndFDerivAt (le_top)).eq (0,z) (1,0)
        rw [hs]; exact (Q.hasFDerivAt.comp_hasDerivAt 0 (hp.hasFDerivAt.comp_hasDerivAt 0 ht)).congr_of_eventuallyEq he
variable [Fintype I][FiniteDimensional ℝ E]
def duty (T:Module.Basis I ℝ E)(p:E→L[ℝ] E):=∑ i:I,T.coord i (p (T i))
lemma port (p:ℝ×E→E) {x:E}(hf:ContDiffAt ℝ ω p (0,x))(B:Module.Basis I ℝ E)(hp:(fun y:E=> p (0,y)) =ᶠ[𝓝 x] id):
    HasDerivAt (fun t:ℝ=> (fderiv ℝ (fun y=> p (t,y)) x).det) (duty B (fderiv ℝ (fun y=>sway p (0,y)) x)) (0:ℝ):=by
       let D(t:ℝ):= fderiv ℝ (fun y=> p (t,y)) x; let J:=fderiv ℝ (fun y=>sway p (0,y)) x; let S:= LinearMap.toMatrix B B
       let V(t:ℝ):=S (D t).toLinearMap
       have he:V 0=1:=by rw [show V 0=S (D 0).toLinearMap from rfl,show D 0=ContinuousLinearMap.id ℝ E from hp.fderiv_eq.trans fderiv_id]; exact LinearMap.toMatrix_id _
       have hv(i j:I): HasDerivAt (fun t=> V t i j) (S J.toLinearMap i j) 0:=by
          unfold V S; simp only [LinearMap.toMatrix_apply]; exact (LinearMap.toContinuousLinearMap (B.coord i)).hasFDerivAt.comp_hasDerivAt 0 (sideways p hf (B j)) -- confirm
       have hm:= det_one_way (M:=V) 0 (S J.toLinearMap) hv (by rw [he,det_one]; norm_num); rw [he,det_one,inv_one,Matrix.one_mul,one_mul] at hm
       rw [show (S J.toLinearMap).trace=duty B J from ?_] at hm; exact hm.congr_of_eventuallyEq (Eventually.of_forall (fun i:ℝ=> (LinearMap.det_toMatrix B (D i).toLinearMap).symm)); unfold S duty trace; simp only [diag_apply, LinearMap.toMatrix_apply]; rfl
end YM.OPE.Variance
