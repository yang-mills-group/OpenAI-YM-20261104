import YM.Integration.WilsonReportingForestCompactAngles
import YM.Integration.WilsonCoherentMeasuredChart
import YM.Integration.WilsonRegisteredAffineRows

/-! The local angular and inherited-support cuts, under one genuine held
Wilson kernel and its original forest chart. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRegisteredAngularGate
open Function Filter Set MeasureTheory Metric Lattice Wilson Tree RG Precision PertExtension
open PhysicalNext.Repeat.Legato MSbar.Heath OPE.Therm RG16
open WilsonPhysicalRegisteredForestAction WilsonReportingForestPivots WilsonCoherentForestMeasure
open WilsonCoherentForestReadout WilsonCoherentMeasuredChart WilsonReportingForestAngularFare Pert.Asymptotics
open scoped Classical Topology
variable {G:Gauge} (R:Run G) {I:Type} [Fintype I]
local notation "A" => R.family.path

def screen (m per:ℕ) (o:I→Site (R.family.side (m+1) per)) (x:Site (R.family.side (m+1) per)) (H:ℕ) :=
  (⋂i,House.chilly (G:=G) (tagCells R m per (o i)) (angularCut ((A).levels.clock.hatBeta (m+1)))) ∩
    House.chilly (WilsonPhysicalHistoryKioskPlaquettes.faces H x) (angularCut ((A).levels.clock.hatBeta (m+1)))

theorem visible (m per:ℕ) (o:I→Site (R.family.side (m+1) per)) (x:Site (R.family.side (m+1) per)) (H:ℕ) :
    MeasurableSet (screen R m per o x H) :=
  (MeasurableSet.iInter (fun _=>House.bath _)).inter (House.bath _)

omit [Fintype I] in
theorem invariant (m per:ℕ) (o:I→Site (R.family.side (m+1) per)) (x:Site (R.family.side (m+1) per))
    (H:ℕ) (a:Site (R.family.side (m+1) per)→G.El) (U:Config G (R.family.side (m+1) per)) :
    Lattice.gauge a U∈screen R m per o x H ↔ U∈screen R m per o x H := by
  simp only [screen,Set.mem_inter_iff,Set.mem_iInter,House.chilly,Set.mem_setOf_eq,face_gauge,G.chord_conj]

def strip (m per:ℕ) (d:I→ℕ) (o:I→Site (R.family.side (m+1) per)) (x:Site (R.family.side (m+1) per)) (H:ℕ)
    (T:Forest ((A).levels.clock.op m per).ratio) (r:ℝ) : Set (Sample T (incident R T d o) G):=
  panel R m per d o T r ∩ state T (incident R T d o) ⁻¹' screen R m per o x H

theorem measurable_strip (m per:ℕ) (d:I→ℕ) (o:I→Site (R.family.side (m+1) per)) (x:Site (R.family.side (m+1) per)) (H:ℕ)
    (T:Forest ((A).levels.clock.op m per).ratio) (r:ℝ) : MeasurableSet (strip R m per d o x H T r):=
  (measurable_panel R m per d o T r).inter ((measurable_state T _) (visible R m per o x H))

theorem radius (simple:G.Simple) (slow:∀m,((R.family.S.block m).val:ℝ)≤Real.log (Lambda (A).levels m))
    (J:Voice G) (clear:Clear G J) (d:I→ℕ) {r:ℝ} (jr:r≤J.r) :
    ∀ᶠ m:ℕ in atTop,∀N (_live:m<N) per (o:I→Site (R.family.side (m+1) per)) (x:Site (R.family.side (m+1) per)) (H:ℕ)
      (T:Forest ((A).levels.clock.op m per).ratio) (z:Sample T (incident R T d o) G),
      z∈strip R m per d o x H T r→ ‖z.2‖≤regulatorRun R.family N per (m+1)*
        ((Real.log ((A).levels.clock.hatBeta (m+1)))^2/32) := by
  filter_upwards [compact_angles R simple slow J clear d] with m angular N live per o x H T z hz
  let k:=m+1
  let β:=(A).levels.clock.hatBeta k
  let g:=regulatorRun R.family N per k
  have bp:0<β:=zero_lt_one.trans ((A).levels.fits.delayed _)
  have band:β/2≤(A).β N per k:=(R.makes.wilson.represents N per k live).band.1
  have gp:0<g:=inv_pos.mpr (Real.sqrt_pos.mpr (by linarith only [bp,band]))
  let Y:=g⁻¹ • z.2
  have cancels:g • Y=z.2:=by rw [smul_inv_smul₀ gp.ne']
  have fit:‖z.2‖≤J.r:=((mem_ball_zero_iff.mp hz.1.1).le).trans jr
  have tp:0≤angularCut β:=by unfold angularCut MSbar.Heath.Stock.cue;positivity [Real.log_pos ((A).levels.fits.delayed k)]
  have q:=angular N live per o T (angularCut β) tp le_rfl z.1 Y (cancels ▸ fit)
    (by rw [cancels];exact Set.mem_iInter.mp hz.2.1)
  calc
    ‖z.2‖=g*‖Y‖:=by rw [←cancels,norm_smul,Real.norm_eq_abs,abs_of_pos gp]
    _≤_:=mul_le_mul_of_nonneg_left q gp.le

theorem physical (simple:G.Simple) (slow:∀m,((R.family.S.block m).val:ℝ)≤Real.log (Lambda (A).levels m))
    (J:Voice G) (clear:Clear G J) (P:ChartRatio G) (hp:LocalRatio P) {r:ℝ} (pr:0<r) (sr:r<Chart.small G P) (d:I→ℕ) :
    ∀ᶠ m:ℕ in atTop,∀N (_live:m<N) per (o:I→Site (R.family.side (m+1) per)) (x:Site (R.family.side (m+1) per)) (H:ℕ)
      (T:Forest ((A).levels.clock.op m per).ratio) (V:Config G (R.family.side m per)) (f:Config G (R.family.side (m+1) per)→ℝ),
    Envelope f→GaugeInvariant f→
    let B:=incident R T d o
    let K:=screen R m per o x H
    let C:=cold R m per d o
    let w:=actualConditionalDensity R.family N per m V
    actualAverage R.family (N:=N) ((C∩K).indicator f) V=
      ∫z in strip R m per d o x H T r,w (state T B z)*f (state T B z) ∂law P r T B := by
  filter_upwards [WilsonCoherentMeasuredChart.observed R simple slow J clear P hp pr sr d] with m chart N live per o x H T V f ef gf
  intro B K C w
  have ms:MeasurableSet K:=visible R m per o x H
  have en:Envelope (K.indicator f):=⟨ef.meas.indicator ms,ef.cost.choose,fun U=>(norm_indicator_le_norm_self f U).trans (ef.cost.choose_spec U)⟩
  have gi:GaugeInvariant (K.indicator f):=by
    intro a U
    have inv:=invariant R m per o x H a U
    by_cases u:U∈K
    · rw [indicator_of_mem (inv.mpr u),indicator_of_mem u,gf]
    · rw [indicator_of_notMem (fun h=>u (inv.mp h)),indicator_of_notMem u]
  have ch:=chart N live per o T V (K.indicator f) en gi
  have signal:C.indicator (K.indicator f)=(C∩K).indicator f:=by
    funext U;by_cases c:U∈C <;> by_cases u:U∈K <;> simp [c,u,Set.indicator]
  change actualAverage R.family (N:=N) (C.indicator (K.indicator f)) V =
    ∫z in panel R m per d o T r,w (state T B z)*K.indicator f (state T B z) ∂law P r T B at ch
  rw [signal] at ch
  rw [ch,strip,←setIntegral_indicator ((measurable_state T B) ms)]
  apply setIntegral_congr_fun (measurable_panel R m per d o T r)
  intro z _
  change w (state T B z)*K.indicator f (state T B z) = _
  by_cases u:state T B z∈K
  · rw [indicator_of_mem u,indicator_of_mem (show z∈state T B ⁻¹' K from u)]
  · rw [indicator_of_notMem u,indicator_of_notMem (show z∉state T B ⁻¹' K from u),mul_zero]

end YM.Integration.WilsonRegisteredAngularGate
end
