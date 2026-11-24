import YM.Integration.WilsonRegisteredAngularGate

/-! Physical disintegration on simultaneous gauge-invariant subevents of
the authentic reporting forest. The saved links have one common law. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRegisteredJoinedScreen
open Function Filter Set MeasureTheory Metric Lattice Wilson Tree RG Precision PertExtension
open PhysicalNext.Repeat.Legato MSbar.Heath OPE.Therm RG16
open WilsonReportingForestPivots WilsonCoherentForestMeasure WilsonCoherentForestReadout WilsonCoherentMeasuredChart
open scoped Classical Topology
variable {G:Gauge} (R:Run G) {I:Type} [Fintype I]
local notation "A" => R.family.path

theorem physical (simple:G.Simple) (slow:∀m,((R.family.S.block m).val:ℝ)≤Real.log (Lambda (A).levels m))
    (J:Voice G) (clear:Clear G J) (P:ChartRatio G) (hp:LocalRatio P) {r:ℝ} (pr:0<r) (sr:r<Chart.small G P) (d:I→ℕ) :
    ∀ᶠ m:ℕ in atTop,∀N (_live:m<N) per (o:I→Site (R.family.side (m+1) per))
      (K:Set (Config G (R.family.side (m+1) per))), MeasurableSet K→
      (∀a U,Lattice.gauge a U∈K↔U∈K)→
      ∀(T:Forest ((A).levels.clock.op m per).ratio) (V:Config G (R.family.side m per)) (f:Config G (R.family.side (m+1) per)→ℝ),
    Envelope f→GaugeInvariant f→
    let B:=incident R T d o
    let C:=cold R m per d o
    let w:=actualConditionalDensity R.family N per m V
    actualAverage R.family (N:=N) ((C∩K).indicator f) V=
      ∫z in panel R m per d o T r ∩ state T B ⁻¹' K,w (state T B z)*f (state T B z) ∂law P r T B := by
  filter_upwards [WilsonCoherentMeasuredChart.observed R simple slow J clear P hp pr sr d] with m chart N live per o K ms inv0 T V f ef gf
  intro B C w
  have en:Envelope (K.indicator f):=⟨ef.meas.indicator ms,ef.cost.choose,fun U=>(norm_indicator_le_norm_self f U).trans (ef.cost.choose_spec U)⟩
  have gi:GaugeInvariant (K.indicator f):=by
    intro a U
    have inv:=inv0 a U
    by_cases u:U∈K
    · rw [indicator_of_mem (inv.mpr u),indicator_of_mem u,gf]
    · rw [indicator_of_notMem (fun h=>u (inv.mp h)),indicator_of_notMem u]
  have ch:=chart N live per o T V (K.indicator f) en gi
  have signal:C.indicator (K.indicator f)=(C∩K).indicator f:=by
    funext U;by_cases c:U∈C <;> by_cases u:U∈K <;> simp [c,u,Set.indicator]
  change actualAverage R.family (N:=N) (C.indicator (K.indicator f)) V =
    ∫z in panel R m per d o T r,w (state T B z)*K.indicator f (state T B z) ∂law P r T B at ch
  rw [signal] at ch
  rw [ch,←setIntegral_indicator ((measurable_state T B) ms)]
  apply setIntegral_congr_fun (measurable_panel R m per d o T r)
  intro z _
  change w (state T B z)*K.indicator f (state T B z) = _
  by_cases u:state T B z∈K
  · rw [indicator_of_mem u,indicator_of_mem (show z∈state T B ⁻¹' K from u)]
  · rw [indicator_of_notMem u,indicator_of_notMem (show z∉state T B ⁻¹' K from u),mul_zero]


end YM.Integration.WilsonRegisteredJoinedScreen
end
