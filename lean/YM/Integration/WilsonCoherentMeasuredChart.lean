import YM.Integration.WilsonCoherentForestReadout
import YM.Integration.WilsonReportingForestPivotConditional

/-! The normalized measured Wilson conditional on its own sampled pairs.
The exterior pivots and the original old vacuum occur inside one integral. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonCoherentMeasuredChart
open Function Filter Finset Set MeasureTheory Metric Lattice RG Wilson Tree Precision PertExtension
open PhysicalNext.Repeat.Legato MSbar.Heath OPE.Therm RG16
open WilsonPhysicalRegisteredForestAction WilsonReportingForestPivots WilsonCoherentForestMeasure WilsonCoherentForestReadout
open scoped Classical Topology

variable {G:Gauge} (R:Run G) {I:Type} [Fintype I]
local notation "A" => R.family.path

def panel (m per:ℕ) (d:I→ℕ) (o:I→Site (R.family.side (m+1) per))
    (T:Forest ((A).levels.clock.op m per).ratio) (r:ℝ) : Set (Sample T (incident R T d o) G) :=
  {z | z.2∈ball 0 r ∧ state T (incident R T d o) z ∈cold R m per d o}

theorem measurable_panel (m per:ℕ) (d:I→ℕ) (o:I→Site (R.family.side (m+1) per))
    (T:Forest ((A).levels.clock.op m per).ratio) (r:ℝ) : MeasurableSet (panel R m per d o T r) := by
  have mc:MeasurableSet (cold R m per d o):=MeasurableSet.iInter (fun _=>House.bath _)
  exact (measurable_snd measurableSet_ball).inter (measurable_state T _ mc)

theorem driver (m per N:ℕ) (live:m<N) (V:Config G (R.family.side m per)) :
    Envelope (actualConditionalDensity R.family N per m V) := by
  obtain ⟨c,hc,lo⟩:=WilsonHeldExteriorLaw.upper_floor R N per m live
  exact (WilsonHeldExteriorLaw.regularity R N per m live V ((A).rep N per (m+1))
    (((A).rep N per (m+1)).envelope (R.makes.wilson.represents N per (m+1) live).good) hc lo).1

theorem observed (simple:G.Simple) (slow:∀m,((R.family.S.block m).val:ℝ)≤Real.log (Lambda (A).levels m))
    (J:Voice G) (clear:Clear G J) (P:ChartRatio G) (hp:LocalRatio P) {r:ℝ} (pr:0<r) (sr:r<Chart.small G P) (d:I→ℕ) :
    ∀ᶠ m:ℕ in atTop,∀N,m<N→∀per (o:I→Site (R.family.side (m+1) per)) (T:Forest ((A).levels.clock.op m per).ratio)
    (V:Config G (R.family.side m per)) (H:Config G (R.family.side (m+1) per)→ℝ),Envelope H→GaugeInvariant H→
    actualAverage R.family (N:=N) ((cold R m per d o).indicator H) V =
    ∫z in panel R m per d o T r,
      let U:=state T (incident R T d o) z
      actualConditionalDensity R.family N per m V U * H U ∂law P r T (incident R T d o) := by
  filter_upwards [WilsonReportingForestPivots.original R simple slow J clear P hp pr sr d] with m fact N live per o T V H eH inv
  let B:=incident R T d o
  let C:=cold R m per d o
  let s:=panel R m per d o T r
  let w:=actualConditionalDensity R.family N per m V
  let F (z:Sample T B G):=w (state T B z) * H (state T B z)
  letI : IsFiniteMeasure (law P r T B) := funded P r T B hp pr sr
  have ms:MeasurableSet s:=measurable_panel R m per d o T r
  have eW:Envelope (fun U=>w U*H U):=(driver R m per N live V).mul eH
  obtain ⟨k,hk⟩:=eW.cost
  have eF:Envelope F:=⟨eW.meas.comp (measurable_state T B),k,fun z=>hk (state T B z)⟩
  have whole:Integrable (s.indicator F) (law P r T B):=(eF.integrable _).indicator ms
  change _ = ∫z in s,F z ∂law P r T B
  rw [←integral_indicator ms,reading P r T B hp pr sr _ whole,fact N live per o T V H eH inv]
  apply integral_congr_ae
  exact ae_of_all _ fun v=>by
    apply setIntegral_congr_fun measurableSet_ball
    intro x hx
    change Chart.jacobian P x * C.indicator (fun U=>w U*H U) (state T B (v,x)) = Chart.jacobian P x*s.indicator F (v,x)
    by_cases h:state T B (v,x)∈C
    · have hc:(v,x)∈s:=⟨hx,h⟩
      rw [Set.indicator_of_mem h,Set.indicator_of_mem hc]
    · have hc:(v,x)∉s:=fun hit=>h hit.2
      rw [Set.indicator_of_notMem h,Set.indicator_of_notMem hc]

end YM.Integration.WilsonCoherentMeasuredChart
