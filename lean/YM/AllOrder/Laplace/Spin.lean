import YM.AllOrder.Laplace.Mechanical
import YM.AnalyticNext.QUARTIC_MATCH.Rephase
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Token.Tune
/-! # Symmetric bill of an *uncut* conditional. Not a formal log price. -/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Laplace
open PertExtension.Series Radial Tested MeasureTheory Function Set Metric Filter
open scoped Topology ENNReal ContDiff Classical
open Lattice Wilson RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented
open PhysicalNext Repeat Lapis Lantern Fare Next.Fluctuations Next.SectorChange
open ConnectedActivityE6 Blaze Brush Poll Coat
open Work.F05 Profiles AnalyticBridge.GaussianFieldAlignment Locations
open AnalyticNext.QuarticMatch.Joint
open scoped BigOperators Matrix.Norms.Frobenius
variable {G:Gauge}{c f n:Side}{S:StepData c f}
variable (F J: Forest S.ratio)(k:S.Choices)(P:ℝ → Config G c)
local notation "K"=>Precision.Key F G

section load
-- Reservoir cost: ANY cut-free hard input model. Incentive for later analytic stencils. No settings postulated.
def rootA (B:ℝ → Config G f→ℝ)(P:ℝ → Config G c) (t:ℝ)(V:Config G f) := B t V+ noiseTaylor S (P t) V k
def poundA (B:ℝ → Config G f→ℝ)(P:ℝ → Config G c) (t:ℝ)(V: F.Slice G):=Real.exp (-rootA k B P t (F.drape V)/t^2)
structure Toll (n : Side) (E:Config G n→ℝ) : Prop where
   fit : Envelope E
   varnish (x : Site n→G.El) (U) : E (gauge x U)=E U
   tilt (s:Signed) (b:Site n) (U) : E (pull s b U)=E U

variable {p : Clip}{R:PathData G}{α T Λ:ℝ}
lemma env_uncut {k:ℕ}{z:ℕ→Atom G k}{σ C:ℝ}(h:SumBudget (fun i=>(z i).budget σ) C)(hp:0<σ) : Envelope (uncut (n:=n) z) := by
   apply Envelope.sum; intro i; exact ⟨Measurable.tsum fun j=> ((z j).unmasked_cont _).measurable, (Dominated.bound (show Dominated (fun j U=> (z j).unmasked U i) from ⟨_,h.2.1.mul_right (2^k),fun a U=> ((z a).unmasked_bound ..).trans (mul_le_mul_of_nonneg_right ((z a).lower_budget σ hp) (by positivity))⟩))⟩
lemma env_price : Envelope G.price := ⟨(by fun_prop),2,fun x=>by rw [Real.norm_of_nonneg (G.price_range _).1]; exact (G.price_range x).2⟩
lemma env_quad (h:R.Bounds p α T Λ) : Envelope (quadratic p R (n:=n)):= by
   unfold quadratic; apply Envelope.sum; intro i
   have he : Envelope fun U=> ‖R.ell U i‖ := by
     obtain ⟨t,ht⟩:= (R.ell_dominated h i).bound; exact ⟨(R.ell_meas _ _ _ _ _ h).norm,t,fun v=> by rw [Real.norm_of_nonneg (norm_nonneg _)]; exact ht _⟩
   simp_rw [pow_two,div_eq_mul_inv]
   exact ((Envelope.const _).mul (Env.along env_price (show (Measurable (fun U => faceValue U i)) from by unfold faceValue; fun_prop))).add ((he.mul he).mul (Envelope.const _))
lemma toll_main (h:R.Bounds p α T Λ): Toll n (mainTerm p R (n:=n)):= by
   refine ⟨?_,fun x a=> mainTerm_gauge h a x,fun s b U=> main_pull p R s b U⟩
   unfold mainTerm Patch.average; exact (Envelope.const _).mul (Envelope.sum _ _ fun i=> ((Env.along (env_quad h) (continuous_pull i 0|>.measurable)).add (Env.along (env_uncut h.three h.width) (continuous_pull i 0|>.measurable))).add (Env.along (env_uncut h.four h.width) (continuous_pull i 0|>.measurable)))
lemma toll_loop (h:R.Bounds p α T Λ): Toll n (Precision.loop R (n:=n)):= by
   refine ⟨?_,fun x U=> loop_gauge h U x,fun s b U=> Token.loopChannel s b R U⟩
   unfold Precision.loop Patch.average; exact (Envelope.const _).mul (Envelope.sum _ _ fun i=> Env.along (env_uncut h.two h.width) (continuous_pull i 0|>.measurable))
lemma Toll.add {e a : Config G n→ℝ}(h:Toll n e)(H:Toll n a): Toll n (e+a):= ⟨h.fit.add H.fit,fun x u=> congr_arg₂ (·+·) (h.varnish x u) (H.varnish x u),fun s b i=> congr_arg₂ (·+·) (h.tilt s b i) (H.tilt s b i)⟩
lemma Toll.scale {e: Config G n→ℝ}(h:Toll n e) (v:ℝ): Toll n (v • e):= ⟨(Envelope.const v).mul h.fit,fun x u=> congr_arg (v*·) (h.varnish x u),fun s b i=> congr_arg (v*·) (h.tilt s b i)⟩

variable {B:ℝ → Config G f→ℝ}(t:ℝ)(h: Toll f (B t)) (hs:S.patch.Branches S.kernel G)
include hs h
lemma env_compel : Envelope (poundA F k B P t) := by
   have he : Envelope (fun U=> noiseTaylor S (P t) U k) := by
      unfold noiseTaylor; refine (Envelope.const _).mul (Envelope.sum _ _ fun i=> Env.along env_price ?_); exact measurable_const.mul ((Measurable.inv ((measurable_pi_apply i).comp (S.prediction_meas hs k))))
   unfold poundA rootA; simp_rw [div_eq_mul_inv]; exact (((Env.along (h.fit.add he) F.continuous_drape.measurable).neg).mul (Envelope.const _)).exp
lemma compel_touch (U:F.Slice G) : poundA J k B P t (Profiles.reroute F J G U)=poundA F k B P t U:= by
   change Real.exp (-rootA k B P t (J.drape (Profiles.wick J (F.drape U)))/_)=_
   rw [wears,wiped,rootA, root_noise hs _ _ _ (fun i=> J.fold_root _ i), h.varnish]; rfl
lemma compel_shift (s:Signed)(b:Site c)(U:F.Slice G) : poundA (Locations.forest s b F) k B ((pull s b)∘ P) t (Turn.glide s b F U)=poundA F (S.withinChoice s b k) B P t U:= by
   unfold poundA rootA; rw [Turn.forward,h.tilt]; unfold noiseTaylor; rw [S.prediction_channel hs s b]; exact congr_arg (fun A=>Real.exp (-(B t (F.drape U)+A)/t^2)) (energy_channel s b S.kernel (S.prediction _ _) (P t))
lemma compel_color (u:ℝ→Site c→G.El) (U:F.Slice G): poundA F k B (fun i=>Lattice.gauge (u i) (P i)) t (fitted F (u t) U)=poundA F k B P t U:= by
   unfold poundA rootA noiseTaylor; dsimp only; rw [worn,h.varnish, AnalyticNext.QuarticMatch.Joint.predicted hs]; rw [show (u t ∘ S.ratio.parent) ∘ S.ratio.embed=u t from ?_] -- orientation
   · exact congr_arg (fun A=> Real.exp (-(B t (F.drape U)+A)/t^2)) (uniform (u t) S.kernel (S.prediction _ _) _)
   ext1 x; simp [S.ratio.embed_parent] -- edit
omit h in
lemma compel_same (k':S.Choices): ∀ᶠ x: F.Slice G in 𝓝 1, ∀ (t :ℝ), poundA F k B P t x=poundA F k' B P t x:= by
   have h: F.drape (1:F.Slice G)=1:= by rw [← Work.F05.exposure_zero F, drape_exposure, Precision.link_one, lifted, replica_one]
   have hh : Tendsto F.drape (𝓝 (1:F.Slice G)) (𝓝 1) := h ▸ F.continuous_drape.continuousAt.tendsto -- sketch
   filter_upwards [hh.eventually (Work.F04.prediction_germ hs k k')] with U H t
   unfold poundA rootA noiseTaylor; rw [show S.prediction (F.drape U) k=S.prediction (F.drape U) k' from H]
end load
end YM.AllOrder.Laplace
