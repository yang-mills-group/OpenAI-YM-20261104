import YM.Integration.WilsonPositionProgramTrialPublicJointPivotMeshRate
import YM.Integration.WilsonPositionScaleLawThermometerOrigin

/-! The appointed thermometer on the original sequence of finite physical torus sites. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionProgramTrialPublicJointPivotMeshThermometer
open Function Set Filter Finset Metric Lattice RG Wilson Source Extraction MeasureTheory PowerSeries
open Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Structure1 XSpace.Rose XSpace.Cirrus XSpace.Photo
open PhysicalNext.Repeat.Legato RG17 Spec Table OPE OPE.Orbits Climb PhysMS Trace.Pilot
open XSpace.Retirement
open MS MS.Land MS.Fleet MS.Book.Program FVA2 FVA2.Register FVA2.Scale FVA2.Arrival
open WilsonPhysicalNormalizedSignedMenu (Row)
open WilsonPositionProgramTrialPublicJointPivotWeights (salary paid)
open WilsonPositionProgramTrialPublicJointPivotSeries (signed)
open WilsonPositionProgramTrialPublicJointPivotMesh (measured)
open WilsonPositionProgramTrialPublicJointPivotMeshStock (mark limit)
open WilsonMaxwellThermometerPublicStation (aperture)
open WilsonOriginalObservedRoseJoint (locations lowerSite)
open WilsonSeparatedOriginalThermometerCells (weight positions placed)
open WilsonReceivedChronologicalFixedRoseVariation (cells)
open WilsonPositionProgramTrialPublicJointPivotMeshCells (panel)
open WilsonPositionProgramTrialPublicJointPivotMeshRate (Dates wage residual)
open WilsonMaxwellThermometerSignedWallet (board)
open WilsonPositionScaleLawThermometerChart (response)
open WilsonPositionScaleLawIndependent (ψ)
open scoped Classical BigOperators Topology
variable {G : Gauge} (R : Run G) (Z : WilsonPrescription G) {hG : G.Simple}
  (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) {σ : Prescription (Press.portDeck G)}
  {dial : Bool} (H : Main.Match Z hG M σ dial) (ν : ℝ)


local notation "φ" => Rose.test Z.criterion
local notation "p" => Rose.tag G
local notation "cT" => (Rose.cT Z.criterion.cut G Z.criterion.image : ℂ)

theorem ground (y : Sample 3) (ready : Z.store.Meets Z.scheme y.F 6) :
    coeff 0 (signed (Rose.measureₓ Z.scheme Z.criterion 6 y) p) = 0 := by
  have rest : coeff 0 (signed (Rose.measureₓ Z.scheme Z.criterion 6 y) p) =
      coeff 0 (signed (Rose.cooked Z.scheme Z.store 6 y) p) := by
    simp [signed,Rose.b3,WilsonPositionProgramTrialPublicJointPivotSeries.whole,coeff_zero_eq_constantCoeff_apply,
      Rose.measure_paid,Rose.turn_rest]
  rw [rest]
  change coeff 0 (Rose.together Z.scheme Z.store y)=0
  have odd := congrArg (coeff (R:=ℂ) 0) (Rose.parity₂ Z.scheme y ready)
  rw [Rose.inversion,coeff_rescale,pow_zero,one_mul,map_neg] at odd
  linear_combination odd/2

theorem actual (r : ℝ) (f per : ℕ) (ready : Z.store.Meets Z.scheme (board R f r per) 6) :
    panel R Z 6 φ r f (f,per) le_rfl 0 p = 0 := by
  rw [WilsonPositionProgramTrialPublicJointPivotMeshCells.occupied]
  unfold WilsonReceivedChronologicalFixedRoseVariation.signed
  apply Finset.sum_eq_zero
  intro y _
  exact mul_eq_zero_of_right _ (ground Z (WilsonOriginalObservedRoseBornAbsolute.cell R φ r f per y) ready)

theorem continuum (k : ℕ) : limit Z M H ν 6 φ k p = cT*coeff k X := by
  have h := WilsonPositionScaleLawThermometerGround.printed Z M H ν 0 k
  rw [WilsonPositionScaleLawThermometerOrigin.clock Z M H ν] at h
  have same : response Z M ν 0=Measure.start Z.scheme Z.criterion 6 := by
    rw [WilsonPositionScaleLawThermometerChart.response,WilsonPositionScaleLawThermometerOrigin.clock Z M H ν,Facets.team_one]
  rw [same] at h
  exact h

theorem printed (q : ℕ) (g : ℂ) :
    ∑ k∈Finset.Icc 1 (q+1),g^k*limit Z M H ν 6 φ k p=cT*g := by
  simp_rw [continuum Z M H ν]
  rw [Finset.sum_eq_single 1]
  · simp [mul_comm]
  · intro k _ ne
    simp [PowerSeries.coeff_X,ne]
  · simp

def reading (r : ℝ) (f per q : ℕ) (g : ℂ) : ℂ :=
  ∑ k∈Finset.range (q+2),g^k*panel R Z 6 φ r f (f,per) le_rfl k p

include M H ν in
theorem original (o : Extraction.Order) (U : Filter (ℕ×ℕ)) (prior : U≤o.fuse) (s : ℝ→ℕ)
    (small : Tendsto (aperture R s) trail (𝓝 0)) (g : Dates→ℂ) (cold : Tendsto g (trail.curry U) (𝓝 0))
    (live : ∀ᶠ w in trail.curry U,g w≠0) (q : ℕ) :
    Tendsto (fun w=>(reading R Z w.1 (s w.1) w.2.2 q (g w)-cT*g w)/g w)
      (trail.curry U) (𝓝 0) := by
  let base := fun _ : Dates=>φ
  let choice := fun _ : Dates=>p
  let B := max 0 (wage base choice (0,0,0))
  have cap : ∀ᶠ w in trail.curry U,wage base choice w≤B := Eventually.of_forall fun _=>le_max_right _ _
  have rate := WilsonPositionProgramTrialPublicJointPivotMeshRate.original R Z M H ν s base choice o U prior small
    (tsupport φ) (Rose.test Z.criterion).hasCompactSupport (Rose.test Z.criterion).tsupport_subset (Eventually.of_forall fun _=>Subset.rfl)
    (le_max_left 0 _) cap g cold live 1 (q+1)
  obtain ⟨_,funds⟩ := WilsonOriginalObservedRoseBornGalopNodes.original R Z φ o U prior s small
  apply rate.congr'
  filter_upwards [funds] with w funded
  have split : Finset.range (q+2)=insert 0 (Finset.Icc 1 (q+1)) := by
    ext k
    simp only [Finset.mem_range,Finset.mem_insert,Finset.mem_Icc]
    omega
  rw [reading,split,Finset.sum_insert (by simp),pow_zero,one_mul,actual R Z _ _ _ funded.1,zero_add,
    ←printed Z M H ν q (g w),pow_one]
  simp only [WilsonPositionProgramTrialPublicJointPivotMeshRate.residual,base,choice,mul_sub,Finset.sum_sub_distrib]

end YM.Integration.WilsonPositionProgramTrialPublicJointPivotMeshThermometer
