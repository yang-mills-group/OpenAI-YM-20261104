import YM.Integration.WilsonPositionProgramTrialPublicJointPivotMeshGap

/-! The signed position and thermometer at the actual reporting mesh on the original regulator filter. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionProgramTrialPublicJointPivotMeshClock
open Function Set Filter Finset Lattice RG Wilson Source Extraction MeasureTheory PowerSeries
open Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Structure1 XSpace.Rose XSpace.Cirrus XSpace.Photo
open PhysicalNext.Repeat.Legato RG17 FullVolume Spec Table OPE OPE.Orbits Climb PhysMS Trace.Pilot
open MS MS.Land MS.Fleet MS.Book.Program FVA2 FVA2.Register FVA2.Scale FVA2.Arrival
open WilsonPhysicalNormalizedSignedMenu (Row positioned docket retag)
open WilsonPhysicalPositionTargetRows (rows)
open WilsonPositionPrescribedScreen (hierarchy)
open WilsonPositionProgramTrialPublicJointPivotNorm (moved)
open WilsonPositionProgramTrialPublicJointPivotMeshGauge (funded)
open WilsonPositionProgramTrialPublicJointPivotMeshCells (panel)
open WilsonPositionProgramTrialPublicJointPivotMeshRate (Dates)
open WilsonPositionProgramTrialPublicJointPivotEvidence (old)
open WilsonMaxwellThermometerPublicStation (aperture)
open WilsonMaxwellThermometerSignedWallet (board)
open scoped Classical BigOperators Topology
variable {G : Gauge} {R : Run G} {o : Extraction.Order} {S : Table R.family.book}
    (F : Final R.family o S) (J : ℝ→PhysMS.tower S) (Z : WilsonPrescription G) {hG : G.Simple}
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) {σ : Prescription (Press.portDeck G)}
    {dial : Bool} (H : Main.Match Z hG M σ dial) (ν : ℝ)

open WilsonPositionProgramTrialPublicJointPivotMeshSlice (film calendar)
open WilsonPositionProgramTrialPublicJointPivotMeshSource (Declared Invested)
open WilsonPositionProgramTrialPublicJointPivotComparison (observed)
local notation "φ" => Rose.test Z.criterion
local notation "tag" => Rose.tag G
local notation "cT" => Rose.cT Z.criterion.cut G Z.criterion.image
local notation "readAt" => WilsonPositionThermometerReading.tested F (WilsonPositionPrescribedFrame.positioned F J Z.store) Z.criterion

theorem entered {r : ℝ} (rp : 0<r)
    (frame : Bijective (stand (WilsonPositionPrescribedScreen.correction F J Z.store 6 r))) :
    observed F J Z φ tag r = readAt r := by
  rw [WilsonPositionProgramTrialPublicJointPivotComparison.observed,dif_pos rp,←WilsonPositionProgramTrialPublicJointPivotEvidence.actual F J Z φ rp tag frame]
  exact WilsonPositionProgramTrialPublicJointPivotLocated.original F J Z.store Z.criterion rp frame

include M H ν in
theorem signed (lead : Leading F J) (U : Filter (ℕ×ℕ)) (prior : U≤o.fuse) (s : ℝ→ℕ)
    (small : Tendsto (aperture R s) trail (𝓝 0)) (q k : ℕ) (g : Dates→ℝ) (cold : Tendsto g (trail.curry U) (𝓝 0))
    (T : Dates→Change G 6) (near : Tendsto (fun w=>guide G 6 (T w)) (trail.curry U) (𝓝 0))
    (V : Dates→Pin G 6→Sec G 6) (same : ∀ᶠ w in trail.curry U, Declared (V w) (T w))
    (B : ℝ) (bp : 0≤B) (e : Dates→ℝ) (live : ∀ᶠ w in trail.curry U, 0<g w ∧ 0≤e w)
    (paid : ∀ᶠ w : Dates in trail.curry U, ∀ (rp : 0<w.1),Invested F J Z s 6 w rp φ q (k+1) (g w) (V w) B (e w))
    (settled : Tendsto (fun w=>e w/g w) (trail.curry U) (𝓝 0)) :
    Tendsto (fun w : Dates=>(readAt w.1-(cT:ℂ)*(g w:ℂ))/(g w:ℂ)) (trail.curry U) (𝓝 0) := by
  have expense := WilsonPositionProgramTrialPublicJointPivotMeshGap.original F J Z M H ν lead U prior s small
    6 φ tag q (k+1) 1 g cold T near V same B bp e live paid (by simpa only [pow_one] using settled)
  simp only [pow_one] at expense
  have gas : Tendsto (fun w=>(g w:ℂ)) (trail.curry U) (𝓝 0) := by
    simpa only [Function.comp_def,Complex.ofReal_zero] using Complex.continuous_ofReal.continuousAt.tendsto.comp cold
  have model := WilsonPositionProgramTrialPublicJointPivotMeshThermometer.original R Z M H ν o U prior s small
    (fun w=>(g w:ℂ)) gas (live.mono fun _ h=>Complex.ofReal_ne_zero.mpr h.1.ne') k
  have combined := expense.add model
  simp only [add_zero] at combined
  apply combined.congr'
  filter_upwards [(calendar U).eventually self_mem_nhdsWithin,
    (calendar U).eventually (WilsonPositionPrescribedScreen.original F J lead Z.store 6).2] with w rp frame
  rw [entered F J Z rp frame.2.1,WilsonPositionProgramTrialPublicJointPivotMeshSlice.applied,
    WilsonPositionProgramTrialPublicJointPivotMeshThermometer.reading]
  ring

theorem numerator (u : ℂ) (g : ℝ) : (u/(g:ℂ)).re=u.re/g := by
  rw [div_eq_mul_inv,←Complex.ofReal_inv,Complex.mul_re]
  simp only [Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,div_eq_mul_inv]

include M H ν in
theorem original (lead : Leading F J) (U : Filter (ℕ×ℕ)) (prior : U≤o.fuse) (s : ℝ→ℕ)
    (small : Tendsto (aperture R s) trail (𝓝 0)) (q k : ℕ) (g : Dates→ℝ) (cold : Tendsto g (trail.curry U) (𝓝 0))
    (T : Dates→Change G 6) (near : Tendsto (fun w=>guide G 6 (T w)) (trail.curry U) (𝓝 0))
    (V : Dates→Pin G 6→Sec G 6) (same : ∀ᶠ w in trail.curry U, Declared (V w) (T w))
    (B : ℝ) (bp : 0≤B) (e : Dates→ℝ) (live : ∀ᶠ w in trail.curry U, 0<g w ∧ 0≤e w)
    (paid : ∀ᶠ w : Dates in trail.curry U, ∀ (rp : 0<w.1),Invested F J Z s 6 w rp φ q (k+1) (g w) (V w) B (e w))
    (settled : Tendsto (fun w=>e w/g w) (trail.curry U) (𝓝 0)) :
    Tendsto (fun w : Dates=>WilsonPositionHomogeneousFrame.reading F J Z w.1/g w) (trail.curry U) (𝓝 1) := by
  have found := signed F J Z M H ν lead U prior s small q k g cold T near V same B bp e live paid settled
  have real : Tendsto (fun w : Dates=>((readAt w.1-(cT:ℂ)*(g w:ℂ))/(g w:ℂ)).re)
      (trail.curry U) (𝓝 0) := by
    simpa only [Function.comp_def,Complex.zero_re] using Complex.continuous_re.continuousAt.tendsto.comp found
  have answer : Tendsto (fun w : Dates=>((readAt w.1-(cT:ℂ)*(g w:ℂ))/(g w:ℂ)).re/cT+1)
      (trail.curry U) (𝓝 1) := by
    simpa only [zero_div,zero_add] using (real.div_const cT).add (tendsto_const_nhds (x:=(1:ℝ)))
  apply answer.congr'
  filter_upwards [live] with w active
  rw [numerator,Complex.sub_re,←Complex.ofReal_mul,Complex.ofReal_re,
    ←WilsonPositionThermometerReading.calibrated_denominator]
  change (cT*WilsonPositionHomogeneousFrame.reading F J Z w.1-cT*g w)/g w/cT+1=_
  field_simp [Z.criterion.fresh.ne,active.1.ne']
  ring

end YM.Integration.WilsonPositionProgramTrialPublicJointPivotMeshClock
