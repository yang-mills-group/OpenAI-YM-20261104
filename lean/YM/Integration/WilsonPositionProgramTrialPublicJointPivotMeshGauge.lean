import YM.Integration.WilsonPositionProgramTrialPublicJointPivotMeshOrdinary

/-! The finite timed position equations absorb one full formal change of the bare programme. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionProgramTrialPublicJointPivotMeshGauge
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


def funded (m : Mesh) (d q : ℕ) (g : ℝ) : Prediction G d :=
  ∑ k∈Finset.range (q+1),g^k • Rose.proposed Z.scheme Z.criterion m d k

theorem value (m : Mesh) (d q : ℕ) (g : ℝ) {n : ℕ} (φ : Test n) (p : Fin n→Sec G d) :
    funded Z m d q g n φ p = ∑ k∈Finset.range (q+1),(g:ℂ)^k*Rose.proposed Z.scheme Z.criterion m d k n φ p := by
  simp only [funded,Finset.sum_apply,Pi.smul_apply,LinearMap.sum_apply,_root_.sum_apply,
    LinearMap.smul_apply,_root_.smul_apply,Complex.real_smul,Complex.ofReal_pow]

theorem coefficient (d k : ℕ) (m : Mesh) (ready : Z.store.Meets Z.scheme m d) :
    (Z.store.measure d).D (Rose.proposed Z.scheme Z.criterion m d k) =
      if k=0 then (Z.store.measure d).D (reference G d) else 0 := by
  rw [Rose.proposed,Rose.turn,_root_.map_sum]
  simp_rw [map_smul,ready.2.1]
  simp [smul_ite,Rose.α,PowerSeries.coeff_one]
  split <;> simp_all

theorem placed (m : Mesh) (d q : ℕ) (g : ℝ) (ready : Z.store.Meets Z.scheme m d) :
    Fray.SetEq (Z.store.measure d) 0 (funded Z m d q g) := by
  rw [Fray.SetEq,stand0,Screen.recruit_one,funded,_root_.map_sum]
  simp_rw [map_smul,coefficient Z d _ m ready]
  simp [smul_ite]

theorem reissued (m : Mesh) (d q : ℕ) (g : ℝ) (ready : Z.store.Meets Z.scheme m d)
    (T : Guard G d) (law : Formal T) (start : constantCoeff T=1) :
    funded Z m d q g = ∑ k∈Finset.range (q+1),g^k • Rose.turn Z.scheme Z.criterion m
      ((Z.store.survey d).fit (Z.store.prepared d) (realm T (batch Z.scheme m d))) k := by
  simp only [funded,Rose.proposed,←Z.store.bare_invariance Z.scheme m d ready T law start]

include H in
theorem stage (d k n : ℕ) (φ : Test n) (p : Fin n→Sec G d) :
    Tendsto (fun m=>Rose.proposed Z.scheme Z.criterion m d k n φ p) Front
      (𝓝 (Reg.Faith.reports ν Z.criterion M d k n φ p)) := by
  simp_rw [Rose.represents,WilsonPositionProgramTrialPublicJointPivotForecast.prescribed Z M H ν]
  exact sees_test (conf n) φ _ (conf_open n) (senses Z M H ν d n k p) (fun _ _ _=>rfl) φ.tsupport_subset

include H ν in
theorem warm {ι : Type*} (u : Filter ι) (m : ι→Mesh) (dates : Tendsto m u Front) (d q : ℕ)
    (g : ι→ℝ) (small : Tendsto g u (𝓝 0)) :
    (Z.store.survey d).Via (u:=u) (fun i=>funded Z (m i) d q (g i)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro a
  let S := (Z.store.survey d).scope i
  let p := fun j => Module.finBasis ℝ (Sec G d) (a j)
  have zero : (∑ k∈Finset.range (q+1),(0:ℂ)^k*Reg.Faith.reports ν Z.criterion M d k S.n S.t p) =
      reference G d S.n S.t p := by
    rw [Finset.sum_eq_single 0]
    · simp [WilsonPositionProgramTrialPublicJointPivotForecast.earned Z M H ν d]
    · intro k _ nz
      simp [zero_pow nz]
    · simp
  have gas : Tendsto (fun j=>(g j:ℂ)) u (𝓝 0) := by simpa only [Function.comp_def,Complex.ofReal_zero] using Complex.continuous_ofReal.continuousAt.tendsto.comp small
  change Tendsto (fun j=>funded Z (m j) d q (g j) S.n S.t p) u (𝓝 (reference G d S.n S.t p))
  simp_rw [value]
  rw [←zero]
  exact tendsto_finsetSum _ fun k _=>(gas.pow k).mul ((stage Z M H ν d k S.n S.t p).comp dates)

include H ν in
theorem original (o : Extraction.Order) (U : Filter (ℕ×ℕ)) (prior : U≤o.fuse) (s : ℝ→ℕ)
    (small : Tendsto (aperture R s) trail (𝓝 0)) (g : ℝ×(ℕ×ℕ)→ℝ)
    (cold : Tendsto g (trail.curry U) (𝓝 0)) (d q : ℕ) :
    ∀ᶠ w : ℝ×(ℕ×ℕ) in trail.curry U,
      let m := board R (s w.1) w.1 w.2.2
      Z.store.Meets Z.scheme m d ∧
      (Z.store.survey d).firstPass (Z.store.prepared d) (funded Z m d q (g w))=0 ∧
      ∀ (T : Guard G d), Formal T → constantCoeff T=1 →
        funded Z m d q (g w) = ∑ k∈Finset.range (q+1),(g w)^k • Rose.turn Z.scheme Z.criterion m
          ((Z.store.survey d).fit (Z.store.prepared d) (realm T (batch Z.scheme m d))) k := by
  let m := fun w : ℝ×(ℕ×ℕ)=>board R (s w.1) w.1 w.2.2
  have dates : Tendsto m (trail.curry U) Front := WilsonSeparatedOriginalThermometerDetectorMesh.reporting
    R trail o U prior s _ (WilsonMaxwellThermometerPublicStation.granted R s) small
  have near := warm Z M H ν (trail.curry U) m dates d q g cold
  have still : Tendsto (fun _ : ℝ×(ℕ×ℕ)=>guide G d (0:Change G d)) (trail.curry U) (𝓝 0) := by
    simpa only [map_zero] using (tendsto_const_nhds (x:=(0:MoveSpace G d)))
  filter_upwards [dates.eventually (Z.store.nested_solution Z.scheme d frontier).2,
    (Z.store.survey d).unmoor (Z.store.prepared d) near (fun _=>0) still] with w ready chosen
  exact ⟨ready.1,chosen.mp (placed Z (m w) d q (g w) ready.1),reissued Z (m w) d q (g w) ready.1⟩

end YM.Integration.WilsonPositionProgramTrialPublicJointPivotMeshGauge
