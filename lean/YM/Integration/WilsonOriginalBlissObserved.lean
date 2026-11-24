import YM.RG17.Gathers
import YM.PhysMS.Frame.Measured
import YM.TraceExtension.Atlas.Global

/-! The inverse source chart on the very ultrafilter of the original physical
trace. It retains the measured finite columns, the reporting calendar and its
engineering power before taking this filter. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalBlissObserved
open Filter RG12 RG17
open scoped Topology Classical
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
  (F:Spec.Final C f S){H:(Climb.Bel C.book).Hierarchy}{l:Ultrafilter (ℕ×ℕ)}
  {arch:Trace.Terrace.Arch C}(bliss:Trace.Pilot.Bliss F l arch H)

theorem column (d k:ℕ)(u:UVIndex)(hk:C.ref d≤k)(live:k≤u.1)(v:C.label d):
    charts C F.room.cutoff d k u v=Trace.Terrace.Cturn C d k u.1 u.2 v:=by
  rw [charts,dif_pos ⟨hk,live⟩]
  rfl

include bliss in
theorem original:Observing C F.room.cutoff (l:Filter UVIndex)
    (fun d k=>(arch.M d k).symm.toLinearMap.toContinuousLinearMap):=by
  have grow:=Trace.Terrace.link_mesh bliss.lies
  refine ⟨grow,?_⟩
  intro d k hk
  have live:=grow.eventually_ge_atTop k
  obtain ⟨c,hc⟩:=atK_fixed_budget C F.room.cutoff d k hk
  obtain ⟨A,limit⟩:=ultrafilter_converges l (atK C F.room.cutoff d k) c
    (live.mono fun u hu=>hc u hu)
  have eq:A=(arch.M d k).symm.toLinearMap.toContinuousLinearMap:=by
    apply ContinuousLinearMap.ext
    intro v
    let b:=(arch.M d k).symm v
    have h₁:Tendsto (fun u:UVIndex=>Trace.Terrace.Cturn C d k u.1 u.2 b)
        (l:Filter UVIndex) (𝓝 v):=by
      simpa only [b,LinearEquiv.apply_symm_apply] using
        bliss.keen.terms d k hk (fun _=>b) b tendsto_const_nhds
    have h₂:Tendsto (fun u:UVIndex=>atK C F.room.cutoff d k u
        (Trace.Terrace.Cturn C d k u.1 u.2 b)) (l:Filter UVIndex) (𝓝 (A v)):=
      (continuous_fst.clm_apply continuous_snd).continuousAt.tendsto.comp
        (limit.prodMk_nhds h₁)
    have h₃:Tendsto (fun _:UVIndex=>b) (l:Filter UVIndex) (𝓝 (A v)):=by
      apply h₂.congr'
      filter_upwards [live] with u hu
      rw [←column F d k u hk hu]
      exact (charts C F.room.cutoff d k u).symm_apply_apply b
    exact (tendsto_nhds_unique (tendsto_const_nhds (x:=b)) h₃).symm
  rwa [←eq]

def layout (J:ℝ→PhysMS.tower S) (level:ℝ→ℕ)
    (shift:∀ d,ℝ→C.label d ≃ₗ[ℂ] C.label d):RG17.Layout F where
  level:=level
  charts:=fun d k=>(arch.M d k).symm.toLinearMap.toContinuousLinearMap
  lens:=l
  notbot:=inferInstance
  certified:=bliss.lies
  observes:=original F bliss
  shift:=shift
  frame:=fun d r=>J r d

theorem measured (J:ℝ→PhysMS.tower S) (level:ℝ→ℕ)
    (shift:∀ d,ℝ→C.label d ≃ₗ[ℂ] C.label d) (d:ℕ)(r:ℝ)(hk:C.ref d≤level r):
    ∀ᶠ u:UVIndex in (l:Filter UVIndex),∀v:C.label d,
      Trace.Terrace.Cturn C d (level r) u.1 u.2
        (atRef (layout F bliss J level shift) d r u v)=
        ((C.S.a (level r)^d:ℝ):ℂ) • shift d r v:=by
  filter_upwards [(Trace.Terrace.link_mesh bliss.lies).eventually_ge_atTop (level r)] with u hu
  intro v
  rw [←column F d (level r) u hk hu]
  change (charts C F.room.cutoff d (level r) u) (_ • (charts C F.room.cutoff d (level r) u).symm _)=_
  rw [map_smul,LinearEquiv.apply_symm_apply]
  rfl

end YM.Integration.WilsonOriginalBlissObserved
