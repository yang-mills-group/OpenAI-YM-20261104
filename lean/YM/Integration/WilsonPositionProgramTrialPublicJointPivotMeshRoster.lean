import YM.Integration.WilsonPositionProgramTrialPublicJointPivotMeshGauge

/-! A common reporting mesh fits all enrolled upper and lower finite prescriptions. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionProgramTrialPublicJointPivotMeshRoster
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
open WilsonPositionProgramTrialPublicJointPivotMesh (senses)
open Position Position.Axes Dframe Level Reg.Point Facets Equator Measure Reg.CoverTest
open WilsonMaxwellThermometerSignedWallet (board)
open scoped Classical BigOperators Topology
variable {G : Gauge} (R : Run G) (Z : WilsonPrescription G) {hG : G.Simple}
  (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) {σ : Prescription (Press.portDeck G)}
  {dial : Bool} (H : Main.Match Z hG M σ dial) (ν : ℝ)


open WilsonPositionProgramTrialPublicJointPivotMeshGauge (funded)

theorem lowered (m : Mesh) {h d : ℕ} (entry : h≤d)
    (hold : ∀ j,Normalize.recruit (up (G:=G) entry) (Z.store.opens Z.scheme m d j)=Z.store.opens Z.scheme m h j)
    (q : ℕ) (g : ℝ) : Normalize.recruit (up entry) (funded Z m d q g)=funded Z m h q g := by
  have step (w : ℝ) (P : Prediction G d) : Normalize.recruit (up entry) (w • P)=w • Normalize.recruit (up entry) P :=
    by rfl
  simp only [funded,Rose.proposed,Rose.turn,_root_.map_sum,step,hold]

include H ν in
theorem original (o : Extraction.Order) (U : Filter (ℕ×ℕ)) (prior : U≤o.fuse) (s : ℝ→ℕ)
    (small : Tendsto (aperture R s) trail (𝓝 0)) (g : ℝ×(ℕ×ℕ)→ℝ) (cold : Tendsto g (trail.curry U) (𝓝 0))
    {I : Type*} [Fintype I] (h d q : I→ℕ) (entry : ∀i,h i≤d i) :
    ∀ᶠ w : ℝ×(ℕ×ℕ) in trail.curry U,
      let m := board R (s w.1) w.1 w.2.2
      ∀ i:I,
        (Z.store.survey (d i)).firstPass (Z.store.prepared (d i)) (funded Z m (d i) (q i) (g w))=0 ∧
        (Z.store.survey (h i)).firstPass (Z.store.prepared (h i)) (funded Z m (h i) (q i) (g w))=0 ∧
        (∀ j t,Normalize.recruit (up (entry i)) (funded Z m (d i) j t)=funded Z m (h i) j t) ∧
        ∀ (T : Guard G (d i)), Formal T → constantCoeff T=1 →
          funded Z m (d i) (q i) (g w)=∑ k∈Finset.range (q i+1),(g w)^k • Rose.turn Z.scheme Z.criterion m
            ((Z.store.survey (d i)).fit (Z.store.prepared (d i)) (realm T (batch Z.scheme m (d i)))) k := by
  have geo : Tendsto (fun w : ℝ×(ℕ×ℕ)=>board R (s w.1) w.1 w.2.2) (trail.curry U) Front :=
    WilsonSeparatedOriginalThermometerDetectorMesh.reporting R trail o U prior s _
      (WilsonMaxwellThermometerPublicStation.granted R s) small
  have timed (j : I→ℕ) := Filter.eventually_all.mpr (fun i=>WilsonPositionProgramTrialPublicJointPivotMeshGauge.original
      R Z M H ν o U prior s small g cold (j i) (q i))
  have cones (i:I) := Z.store.cumulative Z.scheme frontier (entry i)
  filter_upwards [timed d,timed h,geo.eventually (Filter.eventually_all.mpr cones)] with w upper lower own
  dsimp only
  intro i
  exact ⟨(upper i).2.1,(lower i).2.1,lowered Z _ (entry i) (own i),(upper i).2.2⟩

end YM.Integration.WilsonPositionProgramTrialPublicJointPivotMeshRoster
