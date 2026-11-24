import YM.RGComparison.Core16.Halo.Limit
import YM.Pert.Kinetic.Polynomial
import YM.Push.PRICE_COMPILER.Canonical
/-!
# Tangents for calibrating a real representation.

Via ray and limit at any fixed size with its lawful receipts. These read the true exponent near the identity in unmarked sector (outside is still present in the closed exact eval law). Quantitative prices only attached to the readouts, not exchanging with thermodynamic limit.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Catkin
open Function Filter Set Lattice Wilson Exterior RG Precision
open MeasureTheory Halo Lam Pert.Kinetic Work.F03 Lumen AnalyticBridge.VerifiedReset
open scoped Topology BigOperators Classical ContDiff InnerProductSpace Matrix.Norms.Frobenius
variable {G: Gauge} {n f:Side} (hG:G.Simple) {P:BudgetPoint} {σ C Λ δ w:ℝ} {u : ℝ}

variable {R : Rep G n} (H:R.Lawful σ C Λ δ w)

-- apply budget with fixed v first, then remove scale. Not a uniformity claim.
lemma visa (v : Directions G n) : ∃ k:ℝ, 0<k ∧ ∀ o,P.dirBound o (k • v) := by
   have hz: 0<‖v‖+1:=by positivity
   refine ⟨((‖v‖+1)/P.threshold)⁻¹, inv_pos.mpr (div_pos hz P.threshold_pos),fun o=>loose_dir o v hz 0 (Nat.zero_le _) (fun i=>?_)⟩
   rw [pow_zero,mul_one]; exact (norm_le_pi_norm v i).trans (le_add_of_nonneg_right zero_le_one)
include H hG in
lemma account (v : Directions G n): Tendsto (fun t:ℝ=>measuredAction R (AnalyticBridge.VerifiedReset.line v t)/t^2) (𝓝[≠] 0) (𝓝 (meterK R v)) := by
   obtain ⟨k,hk,h⟩:= visa (P:=R.p) v; let u:= k • v
   have hA:= (additive_limit H.labels hG u h).1
   have he : Tendsto (fun t:ℝ=>t/k) (𝓝[≠] 0) (𝓝[≠] 0):= by
      refine tendsto_inf.mpr ⟨((continuous_id.div_const k).tendsto' 0 0 (zero_div _)).mono_left nhdsWithin_le_nhds,tendsto_principal.mpr ?_⟩; exact (show ∀ᶠ z:ℝ in 𝓝[≠] 0,z≠0 from self_mem_nhdsWithin).mono (fun t ht=> div_ne_zero ht hk.ne')
   have hscale t : AnalyticBridge.VerifiedReset.line u (t/k)=AnalyticBridge.VerifiedReset.line v t:=by dsimp only [u,AnalyticBridge.VerifiedReset.line]; rw [smul_smul,div_mul_cancel₀ _ hk.ne']
   have hi:= ((hA.comp he).div_const (k^2)).congr (f₂:=fun t:ℝ=>R.activities.additive R.p (AnalyticBridge.VerifiedReset.line v t)/t^2) (fun t=> by dsimp only [Function.comp_apply]; rw [hscale,div_pow]; field_simp)
   have hh i: logHessian (R.activities.E i) u u/2=k^2*(logHessian (R.activities.E i) v v/2) :=by unfold u; simp only [hessian_eq,map_smul,smul_apply,smul_eq_mul,sq]; ring
   have eh:=multi_tangent H.paths R.beta v; simp_rw [hh,tsum_mul_left, mul_div_cancel_left₀ _ (pow_ne_zero 2 hk.ne'),tsum_div_const] at hi
   refine (eh.add hi).congr' ?_; filter_upwards [(rays_free R.p.threshold R.p.threshold_pos v).filter_mono nhdsWithin_le_nhds] with t ht; unfold measuredAction; rw [PhysicalNext.Repeat.Pane.crystalline _ _ _ _ _ ht]; ring

-- extend to any Apex with its steering Rep, regard as exactly calibrated. Could allow overall scalar (future scales) via charge v only.
structure MetricPort (R:Rep G n)(F : Directions G n → ℝ) : Prop where
    controls : ContDiffAt ℝ 2 F 0
    direct : ∃ x:ℝ, ∀ v, ∀ᶠ t in 𝓝[≠] (0:ℝ), F (t • v) = measuredAction R (AnalyticBridge.VerifiedReset.line v t)+x
variable {F : Directions G n→ℝ} (k: MetricPort R F)
namespace MetricPort
include k
lemma equity (v a:Directions G n) : lend F v a=lend F a v := k.controls.isSymmSndFDerivAt (by simp) ..
include H hG in
lemma bill : fderiv ℝ F 0=0 ∧∀ v, lend F v v=2*meterK R v:=by
    obtain ⟨b,hb⟩:= k.direct
    let A:= fun z=> F z-b; have hd: ContDiffAt ℝ 2 A 0:= k.controls.sub contDiffAt_const
    have he (x:Directions G n) : ContDiffAt ℝ 2 (fun t:ℝ=> A (t • x)) 0:= by exact ((show ContDiffAt ℝ 2 A ((0:ℝ) • x) from (by rw [zero_smul]; exact hd)).comp (f:=fun t:ℝ=>t • x) 0 (contDiffAt_id.smul contDiffAt_const))
    have ht (x:Directions G n): Tendsto (fun t:ℝ=> A (t • x)/t^2) (𝓝[≠] 0) (𝓝 (meterK R x)):= (account hG H x).congr' ((hb x).mono fun t ht=> by dsimp only [A]; rw [ht,add_sub_cancel_right])
    have hm (x):= value_slope_of_sq_limit (he x).continuousAt (ht x)
    have hj : fderiv ℝ A 0=0:=ContinuousLinearMap.ext fun x=> (Push.side A (hd.differentiableAt (by simp)) x).unique (hm x).2
    have hh : fderiv ℝ A = fderiv ℝ F:=by funext y; exact fderiv_sub_const ..
    rw [← hh]; refine ⟨hj,fun v=>?_⟩; have H:= tendsto_nhds_unique (taylor_limit_two (he v) (hm v).1 (hm v).2.deriv) (ht v); rw [line_second hd hj, iteratedFDeriv_two_apply,hh] at H; unfold lend Hess; simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at H; linarith only [H]
end MetricPort
-- compatibility sensor read .Lam
variable {g:ℝ} {S:StepData n f}
lemma chapter (h:S.patch.Branches S.kernel G) (hr:R.eval=S.push (g⁻¹^2) (bare (g⁻¹^2))) : MetricPort R (Lam.centered S g) := by
    let T:= Classical.choice (Tree.select S.ratio S.patch.odd_side); let p:= Next.Fluctuations.Sector.prefactor S G (g⁻¹^2); let A:= collects (G:=G) S T g; have hz:0<p:=pow_pos (inv_pos.mpr (S.penaltyZ_pos _)) _
    refine ⟨?_, -(R.v*(Fintype.card (Site n))),fun v=>?_⟩
    · have he: ContDiff ℝ ∞ (p • A):=(smooth_steps S T h g).const_smul p
      rw [show (Lam.centered S g)=(fun x=> -Real.log ((p • A) x)) from funext fun x=>congrArg (fun u=> -Real.log u) (income S T h g x)]
      exact ((he.of_le (show 2 ≤ (∞:WithTop ℕ∞) from (by decide))).contDiffAt.log (mul_pos hz (Lam.positive S T h g 0)).ne').neg
    filter_upwards [(rays_free R.p.threshold R.p.threshold_pos v).filter_mono nhdsWithin_le_nhds] with t ht; unfold Lam.centered; rw [← hr, show stature (t • v)=AnalyticBridge.VerifiedReset.line v t from funext fun i=>(mul_one (G.lieExp (t • v i))).symm,Rep.eval,Activities.gas_one _ _ ht,mul_one, Real.log_exp]; unfold measuredAction Rep.exponent; ring
end YM.RGComparison.Core16.Catkin
