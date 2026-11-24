import YM.Integration.WilsonPositionProgramTrialPublicJointPivotMeshSource
import YM.Integration.WilsonPositionProgramTrialPublicJointPivotMeshGross
import YM.Integration.WilsonPositionProgramTrialPublicJointPivotComparison

/-! The original signed position estimate is made before division by any power of the measured clock. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionProgramTrialPublicJointPivotMeshGap
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
include H ν in
theorem original (lead : Leading F J) (U : Filter (ℕ×ℕ)) (prior : U≤o.fuse) (s : ℝ→ℕ)
    (small : Tendsto (aperture R s) trail (𝓝 0)) (d : ℕ) (φ : Test 3) (v : Fin 3→Sec G d)
    (q k a : ℕ) (g : Dates→ℝ) (cold : Tendsto g (trail.curry U) (𝓝 0))
    (T : Dates→Change G d) (near : Tendsto (fun w=>guide G d (T w)) (trail.curry U) (𝓝 0))
    (V : Dates→Pin G d→Sec G d) (same : ∀ᶠ w in trail.curry U, Declared (V w) (T w))
    (B : ℝ) (bp : 0≤B) (e : Dates→ℝ) (live : ∀ᶠ w in trail.curry U, 0<g w ∧ 0≤e w)
    (paid : ∀ᶠ w : Dates in trail.curry U, ∀ (rp : 0<w.1),Invested F J Z s d w rp φ q k (g w) (V w) B (e w))
    (settled : Tendsto (fun w=>e w/(g w)^a) (trail.curry U) (𝓝 0)) :
    Tendsto (fun w : Dates=>(observed F J Z φ v w.1-film Z R d φ w.1 (s w.1) w.2.2 k (g w) v)/(g w:ℂ)^a)
      (trail.curry U) (𝓝 0) := by
  obtain ⟨C,cp,price⟩ := WilsonPositionProgramTrialPublicJointPivotMeshSource.original F J Z M H ν lead U prior s small d v
  obtain ⟨L,_,gross⟩ := WilsonPositionProgramTrialPublicJointPivotMeshGross.original (R:=R) Z M H ν o U prior s small d φ
  let K := C*(1+B)*(1+L)
  have ash : Tendsto (fun w=>K*(e w/(g w)^a)) (trail.curry U) (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds (x:=K)).mul settled
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _=>norm_nonneg _) _ ash
  filter_upwards [price q g cold T near,gross k g cold T near,same,live,paid,
    (calendar U).eventually self_mem_nhdsWithin] with w filed total identity earned bill radius
  rw [WilsonPositionProgramTrialPublicJointPivotComparison.observed,dif_pos radius,norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos earned.1]
  have bound := filed radius φ k (V w) identity B (e w) bp earned.2 (bill radius)
  have size := add_le_add (le_refl (1:ℝ)) total
  calc
    _ ≤ (C*((1+B)*e w)*(1+L))/(g w)^a := div_le_div_of_nonneg_right
      (bound.trans (mul_le_mul_of_nonneg_left size (mul_nonneg cp.le (mul_nonneg (by linarith) earned.2))))
      (pow_nonneg earned.1.le a)
    _ = _ := by dsimp only [K]; ring

end YM.Integration.WilsonPositionProgramTrialPublicJointPivotMeshGap
