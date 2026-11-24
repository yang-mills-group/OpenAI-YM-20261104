import YM.Pert.Kinetic.Profile
import YM.Pert.Kinetic.EPrice
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Pane.Null
/-! Complete tested density tangent at held orientation before kinetic extraction. -/
set_option autoImplicit false
noncomputable section
namespace YM.Pert.Kinetic
open Function Filter Set Lattice Wilson Exterior RG Precision
open Work.F03
open scoped Topology BigOperators Classical ContDiff InnerProductSpace Matrix.Norms.Frobenius
variable {n : Side} {G : Gauge} {σ C Λ δ w : ℝ} (R : Rep G n) (hR : R.Lawful σ C Λ δ w)

def measuredAction (U : Config G n) := R.path.inChannels R.clip R.p R.beta U + R.activities.additive R.p U

def meterK (v : Directions G n) := actualPath (p:=R.clip) R.path R.beta v + Eread (A:=R.activities) v /2
include hR
lemma meter_tangent (v : Directions G n) (hG : G.Simple) (hy : ∀ o, R.p.dirBound o v) : Tendsto (fun t:ℝ=> (measuredAction R (AnalyticBridge.VerifiedReset.line v t))/t^2) (𝓝[≠] 0) (𝓝 (meterK R v)) := by
   obtain ⟨he,hs⟩:= additive_limit hR.labels hG v hy
   have hu:= multi_tangent hR.paths R.beta v
   unfold meterK Eread
   rw [← tsum_div_const]
   refine Tendsto.congr' ?_ (hu.add he)
   filter_upwards [(rays_free (G:=G) R.p.threshold R.p.threshold_pos v).filter_mono nhdsWithin_le_nhds] with t ht
   unfold measuredAction
   change ((R.beta*(_)+(_))/t^2 + _/t^2)= _
   rw [PhysicalNext.Repeat.Pane.crystalline _ _ _ _ _ ht]; ring

def rowWave (c : G.Color) (b : Bool) : Directions G n := wave c b 0 1
lemma unscale (c : G.Color) (hc : ‖c‖=1) (b : Bool) (hG : G.Simple) (hn : 4 ≤ n.val) :
     Tendsto (fun t : ℝ => measuredAction R (AnalyticBridge.VerifiedReset.line (rowWave c b) t)/t^2) (𝓝[≠] 0) (𝓝 (meterK R (rowWave c b))) := by
   let v : Directions G n := R.p.threshold • rowWave c b
   have h1 (o) : R.p.dirBound o v := by
      have he:= loose_dir (p:=R.p) o (rowWave c b) zero_lt_one 0 (Nat.zero_le _) (fun e=>by simpa using! wave_bound (i:=0) (j:=1) c hc b hn e)
      simpa only [one_div,inv_inv] using he
   -- easier use tangent twice + congr rescaling identity of both limits (paths harmonic), alternatively additive DCT separately pulling parameter.
   have ha:= additive_limit hR.labels hG v h1
   have ht:=R.p.threshold_pos
   have he : Tendsto (fun t : ℝ=>t/R.p.threshold) (𝓝[≠] 0) (𝓝[≠] 0) := by
      refine tendsto_inf.2 ⟨?_,?_⟩ -- syntax
      · exact ((continuous_id.div_const _).tendsto' 0 0 (zero_div _)).mono_left nhdsWithin_le_nhds
      exact tendsto_principal.mpr ((show ∀ᶠ z : ℝ in 𝓝[≠] 0, z ≠ (0:ℝ) from self_mem_nhdsWithin).mono fun t ht' => div_ne_zero ht' ht.ne')
   have H t : AnalyticBridge.VerifiedReset.line v (t/R.p.threshold) = AnalyticBridge.VerifiedReset.line (rowWave c b) t := by dsimp only [v,AnalyticBridge.VerifiedReset.line]; rw [smul_smul,div_mul_cancel₀ _ ht.ne']
   have ha := ((ha.1.comp he).mul_const (R.p.threshold^2)⁻¹).congr (f₂:=fun t:ℝ=>R.activities.additive R.p (AnalyticBridge.VerifiedReset.line (rowWave c b) t)/t^2) (by intro t; dsimp only [Function.comp_apply]; rw [H];field_simp)
   have hea(i): logHessian (R.activities.E i) v v /2 = R.p.threshold^2*(logHessian (R.activities.E i) (rowWave c b) (rowWave c b)/2) := by
      unfold v; simp only [AnalyticBridge.VerifiedReset.hessian_eq,map_smul,smul_apply,smul_eq_mul,sq]; ring
   simp_rw [hea, tsum_mul_left] at ha
   have ha : Tendsto (fun t:ℝ=>R.activities.additive R.p (AnalyticBridge.VerifiedReset.line (rowWave c b) t)/t^2) (𝓝[≠] 0) (𝓝 (Eread (A:=R.activities) (rowWave c b)/2)) := by
      have ht : Eread (A:=R.activities) (rowWave c b)/2= (R.p.threshold ^ 2 * (∑' (x : ℕ), logHessian (R.activities.E x) (rowWave c b) (rowWave c b) / 2)) * (R.p.threshold^2)⁻¹ := by unfold Eread; rw [tsum_div_const]; field_simp
      rwa [ht]
   refine Tendsto.congr' ?_ ((multi_tangent hR.paths R.beta (rowWave c b)).add ha)
   filter_upwards [(rays_free (G:=G) R.p.threshold R.p.threshold_pos (rowWave c b)).filter_mono nhdsWithin_le_nhds] with t ht
   unfold measuredAction
   change ((R.beta*(_)+(_))/t^2 + _/t^2)= _
   rw [PhysicalNext.Repeat.Pane.crystalline _ _ _ _ _ ht]; ring

end YM.Pert.Kinetic
