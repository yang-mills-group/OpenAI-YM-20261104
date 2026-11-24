import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.LogLink
import YM.Comparison.RG02.Symmetry.Pins
import YM.Comparison.RG02.Adjacent.Rank
import YM.Comparison.RG02.Adjacent.Transport
/-! # Periodic rendering of a Sheet as an actual unmasked supplementary packet
    Period by period, **no locality or cut** assertion. Full *gauge* covariance and VALENCE/
    jet normalization in the actual log chart. The construction may be huge in the period.
    Works also after formal adjacent reset in `Adjacent.Call` or for parts expressed
    directly using a common coupling orientation, when satisfying Sheet.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.Block.Render
open RG Wilson Tree Exterior Lattice Precision MeasureTheory
open Comparison.RG02 Symmetry Symmetry.Orbit Comparison.RG02.Moving Moving.Path Moving.Shift Valence Assembly Adjacent
open Filter Function Set Finset Push.SectorMeasure Gauge CubicMatch Integral ConnectedActivityE6
open PertExtension.Series PertExtension.Series.Tested
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G : Gauge}{n:Side}{E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
attribute [local instance] Gauge.frobInner
local notation "X"=> fieldDir G n 1
local notation "A"=> Config G n
-- torus glob; not committing to long-term physical gauge
private def towards (v:Site n) := route (Lattice.lift (0:Site n)) (Lattice.lift v) 1
private lemma end_t (v:Site n): stop 0 (towards v)=v:=by
   calc _= stop (Lattice.wrap n (Lattice.lift (0:Site n))) (towards v):= by rw [wrap_lift]
        _= wrap n (stop (Lattice.lift (0:Site n)) (towards v)):= (wrap_stop_cover ..).symm
        _=_:= by rw [towards,route_end, wrap_lift]
private def style (U:A) (v:Site n): G.El := travel U 0 (towards v)
def stage (U:A):= gauge (style U) U
lemma fore (t:Site n→G.El)(U:A): stage (gauge t U)=gauge (fun _=> t 0) (stage U):=by
   have hp(v:Site n): style (gauge t U) v= t 0* style U v*(t v)⁻¹:=by unfold style; rw [travel_gauge, end_t]
   ext1 i; unfold stage Lattice.gauge; simp_rw [show ∀ v,style (fun e=> t e.1* U e*_ ) v=_ from hp]; group
lemma style_prep : style (1:A)=1:=by funext p; unfold style; rw [← Precision.link_one]; exact Push.stroll_zero .. 
lemma starts : stage (1:A)=1:= by rw [stage, style_prep]; exact gauge_trivial _
lemma looks : Continuous (stage (G:=G) (n:=n)):=by unfold stage Lattice.gauge style; fun_prop
lemma prep_cont : Continuous (style (G:=G) (n:=n)):= by unfold style; fun_prop

variable {δ γ:ℝ}(f:Chi) (hF:Reliable G δ γ)
def outfit (χ:Chi)(δ:ℝ)(U:A) : X := fun i=> cutLog χ δ (stage U (i.1,axisEquiv.symm i.2))
local notation "Y"=> outfit f δ (G:=G) (n:=n)
include hF
lemma cut_zero : Y 1=0:= by
   unfold outfit; rw [starts]; ext1 i; change cutLog f δ 1 = 0; simp [cutLog]
lemma music (t : Site n→G.El)(U:A): Y (gauge t U) = recolor (t 0) 1 (Y U):=by
    unfold outfit; rw [fore]; funext i; exact hF.conjugate f _ _
lemma cut_conf : Y=ᶠ[𝓝 1] logged ∘ stage:=by
    suffices h: ∀ᶠ x:A in 𝓝 1, ∀ i: Edge (Site n), cutLog f δ (stage x i)= G.plog (G.mat (stage x i)) from h.mono fun _ he=> funext fun i=>he _
    refine eventually_all.mpr fun i=>?_ ; apply Filter.Eventually.mono ((G.continuous_chord.comp (( continuous_apply i ).comp looks)).continuousAt.tendsto.eventually (p:=fun x=>x≤δ) ?_) -- ambiguity
    · exact fun x hx=> hF.kept f _ hx
    change ∀ᶠ t in 𝓝 (G.chord (stage 1 i)), t≤δ; rw [starts]; change ∀ᶠ t in 𝓝 (G.chord 1),_; rw [G.chord_one]; exact ge_mem_nhds hF.down
lemma cut_pan : ContDiffAt ℝ ω ( Y ∘ represent ) 0:=by
    have h : ContDiffAt ℝ ω (fun x:X=>logged (stage (represent x))) 0 := by
       refine logged_smooth (show stage (represent (0:X))=1 from by rw [ Precision.link_one,starts ]) ?_; intro i
       apply CubicMatch.gauged_smooth contDiffAt_id
       intro e; exact YM.AnalyticNext.QuarticMatch.Joint.Smooth.travel (U:=represent) (fun j=> (Work.F03.represent_smooth j).contDiffAt) 0 (towards e)
    refine h.congr_of_eventuallyEq (Filter.EventuallyEq.comp_tendsto (cut_conf f hF) (show Tendsto (represent (G:=G) (n:=n)) (𝓝 0) (𝓝 1) from ?_)); rw [← Precision.link_one]; exact (by unfold represent increment Exterior.collect; fun_prop : Continuous (represent (G:=G) (n:=n))).continuousAt
lemma lawful : Continuous Y:=by
   have he : Continuous (cutLog f δ (G:=G)) := by
      rw [continuous_iff_continuousAt]; intro u; by_cases hx : G.chord u ≤ 2*δ
      · have hp : ContinuousAt (fun v : G.El => f.innerShare δ (G.chord v)) u := by
          unfold Chi.innerShare; exact (f.smooth.continuous.comp (f:=fun v : G.El => (G.chord v/δ)^2) (by fun_prop)).continuousAt
        exact hp.smul ((hF.patch _ hx).continuousAt.comp (f:=G.mat) G.continuous_mat.continuousAt)
      refine ContinuousAt.congr (f := fun _ : G.El => (0:G.Color)) continuousAt_const ?_
      have ht : ∀ᶠ v in 𝓝 u, 2*δ < G.chord v := G.continuous_chord.continuousAt.eventually
        (lt_mem_nhds (lt_of_not_ge hx))
      filter_upwards [ht] with v hv
      have hk : f.innerShare δ (G.chord v)=0 := by
        by_contra hu; exact (f.chosen_lt _ _ hF.down hu).not_ge hv.le
      rw [cutLog,hk,zero_smul]
   exact continuous_pi fun i=> he.comp ((continuous_apply _).comp looks)
omit hF
variable (γ' : ℝ→ fieldDir G n 1)
def read : ℝ→ X := dslope (fun t=> Y (sample t (γ' t))) 0
include hF
variable (hγ : glows γ')
lemma tends_ne : ∀ t:ℝ, t • read f (δ:=δ) γ' t= Y (sample t (γ' t)):= by
   intro t; unfold read; apply (show _ from ?_); simpa [sample, Precision.link_one, cut_zero f hF] using sub_smul_dslope (fun t=> Y (sample t (γ' t))) 0 t
include hγ
lemma readingPane : glows (read f (δ:=δ) γ'):=by
    have he: ContDiffAt ℝ ω (fun t=> Y (sample t (γ' t))) 0:= ContDiffAt.comp (g:=Y ∘ represent) (f:=fun t:ℝ=> t • γ' t) 0 ((zero_smul ℝ (γ' 0)).symm ▸ (cut_pan f hF)) (contDiffAt_id.smul hγ)
    obtain ⟨p,hp⟩:= he.analyticAt; exact (show AnalyticAt ℝ (read f γ') 0 from ⟨_,hp.has_fpower_series_dslope_fslope⟩).contDiffAt
lemma followsR : Flow (read f (δ:=δ) γ') γ':=by
    let V(t:ℝ):= sample t (γ' t)
    have hv:Tendsto V (𝓝 0) (𝓝 1):= by
       have h':ContinuousAt V 0:= by unfold V sample; exact ((by unfold represent increment Exterior.collect; fun_prop: Continuous (represent (G:=G) (n:=n))).continuousAt.comp (continuousAt_id.smul hγ.continuousAt))
       have he:V 0=1:=by unfold V sample; rw [zero_smul, Precision.link_one]
       rw [← he]; exact h'
    have hg: Tendsto (fun t=> style (V t)) Laplace.along (𝓝 1):= ( (prep_cont.tendsto' 1 1 style_prep).comp hv).mono_left nhdsWithin_le_nhds
    refine ⟨1,fun t=>style (V t),hg,?_⟩
    have hu:= cut_conf (n:=n) f hF
    suffices he : ∀ᶠ t in 𝓝 0,sample t (read f (δ:=δ) γ' t)=stage (V t) from he.filter_mono nhdsWithin_le_nhds
    have hz : ∀ i:Edge (Site n), ∀ᶠ t in 𝓝 (0:ℝ), G.lieExp (G.plog (G.mat (stage (V t) i)))=stage (V t) i:=fun i=> ((( continuous_apply i ).tendsto (1:A)).comp ((looks.tendsto' 1 1 starts).comp hv)).eventually G.plog_right
    filter_upwards [hv.eventually hu,eventually_all.mpr hz] with t ht hh; ext1 i
    rw [sample,tends_ne f hF γ']; change represent (Y (V t)) i=_; rw [ht,Function.comp_apply,Work.F03.represent_link, CubicMatch.logged]; dsimp only; rw [show axisEquiv.symm (coord i.2)= i.2 from axisEquiv.symm_apply_apply _]; exact hh i
end YM.FVAAlt2.Block.Render
