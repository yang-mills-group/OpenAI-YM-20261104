import YM.Qlocal.Quipu.Lasso
import YM.AllOrder.Haiku.Projection
/-!
Polynomial recovery of the logarithms of neutral words uses only the curvature
 slot of the group. Mat extension defined on ALL real and complex
 inputs later, not asking for plog to have it.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Quipu.Lasso
open Function Filter Lattice Laurent RG Wilson Stationary Metric Work
open scoped Topology BigOperators Classical ENNReal ContDiff Matrix.Norms.Frobenius
variable (G:Gauge)

def peach (x:G.Color):= G.curvature (G.lieExp x)
@[simp] lemma peach_zero : peach G 0=0:= by simp [peach]
lemma peachCont : ContDiff ℝ ω (peach G):= by
   let L:=G.projectColor.toContinuousLinearMap
   change ContDiff ℝ ω (fun x=> L ((1/2:ℝ) • (G.mat (G.lieExp x)-G.mat (G.lieExp x)⁻¹))); simp_rw [G.mat_inv]; exact L.contDiff.comp ((G.exp_jet.sub (((starL ℝ : G.Mat ≃L[ℝ] G.Mat).contDiff).comp G.exp_jet)).const_smul _)
lemma peachAt : HasFDerivAt (peach G) ((ContinuousLinearEquiv.refl ℝ G.Color): G.Color→L[ℝ] G.Color) 0:= by
   have hh:= (peachCont G).differentiable (by simp) (0:G.Color); have hx: fderiv ℝ (peach G) 0= (ContinuousLinearEquiv.refl ℝ G.Color).toContinuousLinearMap:= by ext1 x; exact (Push.side _ hh x).unique (G.leading_curvature x)
   rw [← hx]; exact hh.hasFDerivAt
lemma peachMove (u:G.El)(x:G.Color):peach G (G.adjoint u x)= G.adjoint u (peach G x):= by unfold peach; rw [← G.curvature_conjugate]; exact congr_arg _ (Stationary.adjoint_exp ..) -- name
private abbrev buoy (G:Gauge):OpenPartialHomeomorph G.Color G.Color:= (peachCont G|>.contDiffAt (x:=0)).toOpenPartialHomeomorph _ (peachAt G) (by simp)
private lemma staysIn : (0:G.Color)∈ (buoy G).source:= ContDiffAt.mem_toOpenPartialHomeomorph_source ..
private lemma staysOut : (0:G.Color)∈ (buoy G).target:= by rw [← peach_zero G]; exact ContDiffAt.image_mem_toOpenPartialHomeomorph_target ..

def carryOn (G:Gauge) : G.Color→ G.Color := (buoy G).symm
@[simp] lemma carry0: carryOn G 0=0:= by
   conv_lhs=>arg 2; rw [← peach_zero G]
   exact (buoy G).left_inv (staysIn G) -- sep
lemma carry_spark : ContDiffAt ℝ ω (carryOn G) 0:= by
   have h := ((peachCont G).contDiffAt (x:=0)).to_localInverse (peachAt G) (show ω ≠ (0 : WithTop ℕ∞) by simp)
   rw [peach_zero] at h; exact h
lemma carry_origin : ∀ᶠ x in 𝓝 (0:G.Color), carryOn G (peach G x)=x:= Eventually.mono ((buoy G).open_source.mem_nhds (staysIn G)) fun _ hx=> (buoy G).left_inv hx
lemma carry_old (u:G.El) : ∀ᶠ x in 𝓝 (0:G.Color), carryOn G (G.adjoint u x)=G.adjoint u (carryOn G x):= by
   let f:= (G.adjoint u).toContinuousLinearMap; have hx: Tendsto (carryOn G) (𝓝 0) (𝓝 0):= by simpa using (carry_spark G).continuousAt.tendsto
   filter_upwards [(buoy G).open_target.mem_nhds (staysOut G), hx.eventually ((show Tendsto f (𝓝 0) (𝓝 0) from by simpa using f.continuous.tendsto 0).eventually (carry_origin G))] with x hu hv; have hg : peach G (carryOn G x)=x:= (buoy G).right_inv hu
   change carryOn G (peach G (G.adjoint u _))= _ at hv; rw [peachMove,hg] at hv; exact hv

def theta (n:ℕ) := G05.blockTaylor n (carryOn G)
@[simp] lemma thetaZero n :theta G n 0 = 0:= by rw [theta,G05.blockTaylor_zero,carry0]
lemma theta_cont (n:ℕ): ContDiff ℝ ω (theta G n):= G05.blockTaylor_contDiff ..
lemma theta_moves (n:ℕ)(u:G.El)(x:G.Color):theta G n (G.adjoint u x)= G.adjoint u (theta G n x):= G05.blockTaylor_equivariant ((carry_spark G).of_le le_top) (G.adjoint u).toContinuousLinearMap (G.adjoint u).toContinuousLinearMap (carry_old G u) x
lemma theta_held (n:ℕ): ∃ C≥0,∀ x:G.Color, ‖x‖ ≤ 2 → ‖theta G n x‖ ≤ C*‖x‖:= by
    let T:=theta G n; let X:= closedBall (0:G.Color) 2; have hm : IsCompact X:= isCompact_closedBall ..
    have hc : Continuous fun x=> ‖fderiv ℝ T x‖:=((theta_cont G n).continuous_fderiv (by simp)).norm
    obtain ⟨b,h⟩:= (hm.image hc).bddAbove
    have hp:(0:G.Color)∈X:= mem_closedBall_self (by norm_num); refine ⟨b,(norm_nonneg (fderiv ℝ T 0)).trans (h ⟨0,hp,rfl⟩),fun x hx=>?_⟩
    have hx : x∈X:= by simpa [X] using hx
    let H:= Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜:=ℝ) (f:=T) (fun x _=>(theta_cont G n).differentiable (by simp) x) (fun x hx=> h ⟨x,hx,rfl⟩) (convex_closedBall 0 2) hp hx -- syntax
    simpa only [T,thetaZero,sub_zero,mul_comm,norm_neg] using H

-- any analytic group germ (also periodized) at center
variable {Y:Type*}[NormedAddCommGroup Y][NormedSpace ℝ Y]
variable {U:Y→G.El}
lemma curve_c (ht:ContDiffAt ℝ ω (fun y=>G.mat (U y)) 0): ContDiffAt ℝ ω (G.curvature ∘ U) 0:= by
   unfold Gauge.curvature Function.comp; simp_rw [G.mat_inv]; exact G.projectColor.toContinuousLinearMap.contDiff.contDiffAt.comp _ ((ht.sub ((starL ℝ : G.Mat ≃L[ℝ] G.Mat).contDiff.contDiffAt.comp _ ht)).const_smul _)
lemma legacy (t:ℕ)(hU:U 0=1)(ht:ContDiffAt ℝ ω (fun y=>G.mat (U y)) 0)(j:ℕ)(hj:j ≤ t): iteratedFDeriv ℝ j (theta G t ∘ G.curvature ∘ U) 0=iteratedFDeriv ℝ j (G.plog ∘ G.mat ∘ U) 0 := by
   let f:Y→G.Mat:=fun y=>G.mat (U y); let g:=G.curvature ∘ U; have hg : ContDiffAt ℝ ω g 0:= curve_c G ht
   have he:f 0=1:= (by simp [f,hU]); have hs:ContDiffAt ℝ ω (G.plog ∘ f) 0:= ContDiffAt.comp _ (by rw [he]; exact G.plog_diff) ht
   have hv : Tendsto U (𝓝 0) (𝓝 1) := by
       apply ((G.continuous_mat.isClosedEmbedding G.mat_injective).tendsto_nhds_iff.mpr); change Tendsto f _ _; rw [← hU,show G.mat _=f 0 from rfl]; exact ht.continuousAt.tendsto
   have hk : Tendsto (G.plog ∘ f) (𝓝 0) (𝓝 0):=by simpa [he] using hs.continuousAt.tendsto
   have hh : (carryOn G ∘ g) =ᶠ[𝓝 0] (G.plog ∘ f) := by
       filter_upwards [hv.eventually G.plog_right,hk.eventually (carry_origin G)] with x hx hy
       change carryOn G (G.curvature (G.lieExp (G.plog (G.mat (U x)))))=_ at hy
       rw [hx] at hy; exact hy
   have hz:g 0=0:= by simp [g,hU]
   change iteratedFDeriv _ _ (theta G t ∘ g) _=_
   rw [show iteratedFDeriv ℝ j (theta G t ∘ g) 0 = iteratedFDeriv ℝ j (carryOn G ∘ g) 0 from G05.jets_comp (hg.of_le le_top) (hg.of_le le_top) (((theta_cont G t).contDiffAt).of_le le_top) (hz.symm ▸ (carry_spark G).of_le le_top) rfl (fun _ _=>rfl) (fun i hi=>by rw [hz]; exact G05.blockTaylor_jets ((carry_spark G).of_le le_top) i hi) _ hj]; exact (hh.iteratedFDeriv ℝ j).eq_of_nhds
end YM.Qlocal.Quipu.Lasso
