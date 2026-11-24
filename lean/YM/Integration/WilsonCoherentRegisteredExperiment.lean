import YM.Integration.WilsonCoherentMeasuredChart
import YM.Integration.WilsonCoherentMeasuredStencil
import YM.Integration.WilsonCoherentSignedIntegral

/-! The original normalized conditional and its registered pivot Taylor
polynomial on the same cut, with the complete correlated spectator. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonCoherentRegisteredExperiment
open Function Filter Finset Set MeasureTheory Metric Lattice RG Wilson Tree Precision PertExtension
open PhysicalNext.Repeat.Legato MSbar.Heath OPE.Therm RG16 Pert.Asymptotics
open WilsonReportingForestPivots WilsonCoherentForestMeasure WilsonCoherentForestReadout
open WilsonIncidentRegisteredMass WilsonCoherentMeasuredStencil WilsonCoherentMeasuredChart
open scoped Classical Topology
variable {G:Gauge} (R:Run G) {I:Type} [Fintype I]
local notation "A" => R.family.path

theorem measured (simple:G.Simple) (slow:∀m,((R.family.S.block m).val:ℝ)≤Real.log (Lambda (A).levels m))
    (J:Voice G) (clear:Clear G J) (P:ChartRatio G) (hp:LocalRatio P) {r:ℝ} (pr:0<r) (sr:r<Chart.small G P)
    (d:I→ℕ) (q:ℕ) {ε:ℝ} (he:0<ε) :
    ∀ᶠ m:ℕ in atTop,∀ N per,m+1≤N→∀(y:∀i,R.family.label (d i)) (o:I→Site (R.family.side (m+1) per))
    (T:Forest ((A).levels.clock.op m per).ratio) (V:Config G (R.family.side m per))
    (c:ℂ) (χ:ℂ→L[ℝ]ℝ) (H:Config G (R.family.side (m+1) per)→ℝ),Envelope H→GaugeInvariant H→
    let B:=incident R T d o
    let θ:=((A).rep N per (m+1)).p.threshold
    let C:=cold R m per d o
    let actual (U:Config G (R.family.side (m+1) per)):=χ (c*∏i,Push.Local.primary (R.family.localSection (d i)) (o i) θ (y i) U)
    let g:=regulatorRun R.family N per (m+1)
    let filed:=∫z in panel R m per d o T r,
      let U:=state T B z
      actualConditionalDensity R.family N per m V U * H U *
        χ (c*polynomial T B R d θ y o (q+2*reserve R d) z) ∂law P r T B
    |actualAverage R.family (N:=N) (C.indicator (fun U=>H U*actual U)) V-filed|≤
      ((‖χ‖*‖c‖)*(ε*g^q*originalMass R d y))*actualAverage R.family (N:=N) (C.indicator (fun U=>|H U|)) V := by
  filter_upwards [WilsonCoherentMeasuredChart.observed R simple slow J clear P hp pr sr d,
    on_event R d simple,WilsonCoherentMeasuredStencil.purchased R d simple slow J clear P pr sr q he]
    with m chart same pay N per live y o T V c χ H eH gH
  intro B θ C actual g filed
  let s:=panel R m per d o T r
  let μ:=law P r T B
  let w:=actualConditionalDensity R.family N per m V
  let U:=state (G:=G) T B
  let h (z:Sample T B G):=w (U z)*H (U z)
  let f:=mark R d o θ y c χ
  let a (z:Sample T B G):=χ (c*polynomial T B R d θ y o (q+2*reserve R d) z)
  let K:=(‖χ‖*‖c‖)*(ε*g^q*originalMass R d y)
  letI : IsFiniteMeasure μ:=funded P r T B hp pr sr
  have ms:MeasurableSet s:=measurable_panel R m per d o T r
  have mu:Measurable U:=measurable_state T B
  obtain ⟨ef,gf⟩:=legitimate R d o θ y c χ
  have ew:Envelope w:=driver R m per N live V
  have eh:Envelope h:=⟨(ew.mul eH).meas.comp mu,(ew.mul eH).cost.imp fun _ a z=>a (U z)⟩
  have eu:Envelope (f∘U):=⟨ef.meas.comp mu,ef.cost.imp fun _ a z=>a (U z)⟩
  have mhabs:Envelope (fun u=>|H u|):=⟨eH.meas.abs,eH.cost.imp fun _ a u=>by simpa using a u⟩
  have yes (z) (hz:z∈s):‖f (U z)-a z‖≤K:=pay N per live y o T c χ z hz.1 hz.2
  have ma:Measurable a:=χ.continuous.measurable.comp
    ((measurable_polynomial T B R d θ y o (q+2*reserve R d)).const_mul c)
  have bill:=WilsonCoherentSignedIntegral.comparison (μ:=μ.restrict s) (H:=h) (F:=f∘U) (P:=a) (K:=K)
    (eh.integrable _) ((eh.mul eu).integrable _) eu.meas.aestronglyMeasurable ma.aestronglyMeasurable
    ((ae_restrict_mem ms).mono yes)
  have hg (b u): H (Lattice.gauge b u)*f (Lattice.gauge b u)=H u*f u:=congrArg₂ (·*·) (gH b u) (gf b u)
  have first:=chart N live per o T V (fun u=>H u*f u) (eH.mul ef) hg
  have last:=chart N live per o T V (fun u=>|H u|) mhabs (fun b u=>congrArg abs (gH b u))
  have eq:C.indicator (fun u=>H u*actual u)=C.indicator (fun u=>H u*f u):=by
    funext u
    by_cases hu:u∈C
    · rw [indicator_of_mem hu,indicator_of_mem hu]
      exact congrArg (fun t:ℂ=>H u*χ (c*t)) (same N per live o y u hu).symm
    · rw [indicator_of_notMem hu,indicator_of_notMem hu]
  have total : (∫z in s,|h z| ∂μ)=actualAverage R.family (N:=N) (C.indicator (fun u=>|H u|)) V:=by
    rw [last]
    apply setIntegral_congr_fun ms
    intro z _
    exact (abs_mul _ _).trans (by rw [abs_of_nonneg (actualConditionalDensity_nonneg R.family R.makes live V (U z))])
  rw [eq,first]
  rw [←total]
  simpa only [filed,h,f,a,g,K,U,μ,s,Function.comp_apply,mul_assoc] using bill

end YM.Integration.WilsonCoherentRegisteredExperiment
