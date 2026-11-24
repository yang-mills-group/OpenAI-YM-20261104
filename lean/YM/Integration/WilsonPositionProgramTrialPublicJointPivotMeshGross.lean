import YM.Integration.WilsonPositionProgramTrialPublicJointPivotMeshSlice

/-! The entire finite array on the measured mesh stays bounded before the position estimate is divided by the clock. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionProgramTrialPublicJointPivotMeshGross
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

open WilsonPositionProgramTrialPublicJointPivotMeshSlice (film)
open WilsonPositionProgramTrialPublicJointPivotMeshStock (limit)
open WilsonPositionProgramTrialPublicJointPivotMeshRate (residual wage)

theorem sampled (o : Extraction.Order) (U : Filter (ℕ×ℕ)) (prior : U≤o.fuse) (s : ℝ→ℕ)
    (small : Tendsto (aperture R s) trail (𝓝 0)) (d : ℕ) (φ : Test 3) (q : ℕ)
    (g : Dates→ℝ) (cold : Tendsto g (trail.curry U) (𝓝 0)) :
    Tendsto (fun w : Dates=>rows (film Z R d φ w.1 (s w.1) w.2.2 q (g w))) (trail.curry U)
      (𝓝 (rows (WilsonPositionProgramTrialPublicJointPivotMeshStock.limit Z M H ν d φ 0))) := by
  apply tendsto_pi_nhds.mpr
  intro b
  let v := fun j=>Module.finBasis ℝ (Sec G d) (b j)
  let L := fun k=>WilsonPositionProgramTrialPublicJointPivotMeshStock.limit Z M H ν d φ k v
  have cap : ∀ᶠ w : Dates in trail.curry U, wage (fun _:Dates=>φ) (fun _:Dates=>v) w ≤
      max 0 (wage (fun _:Dates=>φ) (fun _:Dates=>v) (0,0,0)) := Eventually.of_forall fun _=>le_max_right _ _
  have entry (k : ℕ) : Tendsto (fun w : Dates=>panel R Z d φ w.1 (s w.1) (s w.1,w.2.2) le_rfl k v)
      (trail.curry U) (𝓝 (L k)) := by
    have tail := WilsonPositionProgramTrialPublicJointPivotMeshRate.coefficient R Z M H ν s (fun _:Dates=>φ)
      (fun _:Dates=>v) o U prior small (tsupport φ) φ.hasCompactSupport φ.tsupport_subset
      (Eventually.of_forall fun _=>Subset.rfl) (le_max_left 0 _) cap k
    simpa only [WilsonPositionProgramTrialPublicJointPivotMeshRate.residual,Pi.add_apply,L,sub_add_cancel,zero_add] using tail.add (tendsto_const_nhds (x:=L k))
  have start : ∑ k∈Finset.range (q+1),(0:ℂ)^k*L k=L 0 := by
    rw [Finset.sum_eq_single 0]
    · simp
    · intro k _ nk
      simp [zero_pow nk]
    · simp
  have gas : Tendsto (fun w=>(g w:ℂ)) (trail.curry U) (𝓝 0) := by
    simpa only [Function.comp_def,Complex.ofReal_zero] using Complex.continuous_ofReal.continuousAt.tendsto.comp cold
  change Tendsto (fun w : Dates=>film Z R d φ w.1 (s w.1) w.2.2 q (g w) v) (trail.curry U) (𝓝 (L 0))
  simp_rw [WilsonPositionProgramTrialPublicJointPivotMeshSlice.applied]
  rw [←start]
  exact tendsto_finsetSum _ fun k _=>(gas.pow k).mul (entry k)

include M H ν in
theorem original (o : Extraction.Order) (U : Filter (ℕ×ℕ)) (prior : U≤o.fuse) (s : ℝ→ℕ)
    (small : Tendsto (aperture R s) trail (𝓝 0)) (d : ℕ) (φ : Test 3) :
    ∃ L : ℝ, 0<L ∧ ∀ (q : ℕ) (g : Dates→ℝ) (_ : Tendsto g (trail.curry U) (𝓝 0))
      (T : Dates→Change G d) (_ : Tendsto (fun w=>guide G d (T w)) (trail.curry U) (𝓝 0)),
      ∀ᶠ w : Dates in trail.curry U, ‖rows (moved (T w) (film Z R d φ w.1 (s w.1) w.2.2 q (g w)))‖≤L := by
  let A := ‖rows (WilsonPositionProgramTrialPublicJointPivotMeshStock.limit Z M H ν d φ 0)‖
  refine ⟨2*(A+1),by dsimp only [A]; positivity,?_⟩
  intro q g cold T near
  have bounded := (tendsto_order.mp (sampled Z M H ν o U prior s small d φ q g cold).norm).2 (A+1)
    (by change A<A+1;linarith)
  filter_upwards [bounded,WilsonPositionProgramTrialPublicJointPivotNorm.drift (n:=3) _ T near] with w capped active
  let W := film Z R d φ w.1 (s w.1) w.2.2 q (g w)
  have cap : ‖rows W‖<A+1 := capped
  have error := active W
  have top := norm_le_norm_sub_add (rows (moved (T w) W)) (rows W)
  change ‖rows (moved (T w) W)‖≤_
  linarith [norm_nonneg (rows W)]

end YM.Integration.WilsonPositionProgramTrialPublicJointPivotMeshGross
