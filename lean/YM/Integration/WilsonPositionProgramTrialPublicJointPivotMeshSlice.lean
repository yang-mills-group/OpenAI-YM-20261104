import YM.Integration.WilsonPositionProgramTrialPublicJointPivotMeshRoster
import YM.Integration.WilsonPositionProgramTrialPublicJointPivotMeshThermometer
import YM.Integration.WilsonPositionProgramTrialPublicJointPivotEvidence

/-! The physical position equations on the same finite board as the fully tested seven-face array. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionProgramTrialPublicJointPivotMeshSlice
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

def film (R : Run G) (d : ℕ) (φ : Test 3) (r : ℝ) (f per q : ℕ) (g : ℝ) : Row G d 3 :=
  ∑ k∈Finset.range (q+1),(g:ℂ)^k • panel R Z d φ r f (f,per) le_rfl k

theorem applied (d : ℕ) (φ : Test 3) (r : ℝ) (f per q : ℕ) (g : ℝ) (v : Fin 3→Sec G d) :
    film Z R d φ r f per q g v = ∑ k∈Finset.range (q+1),(g:ℂ)^k*panel R Z d φ r f (f,per) le_rfl k v := by
  simp only [film,_root_.sum_apply,_root_.smul_apply,smul_eq_mul]

theorem calendar (U : Filter (ℕ×ℕ)) : Tendsto (@Prod.fst ℝ (ℕ×ℕ)) (trail.curry U) trail := by
  apply tendsto_def.mpr
  intro a entered
  exact eventually_curry_iff.mpr ((show ∀ᶠ r in trail,r∈a from entered).mono fun _ h=>Eventually.of_forall fun _=>h)

include H ν in
theorem original (lead : Leading F J) (U : Filter (ℕ×ℕ)) (prior : U≤o.fuse) (s : ℝ→ℕ)
    (small : Tendsto (aperture R s) trail (𝓝 0)) (d : ℕ) (v : Fin 3→Sec G d) :
    ∃ C : ℝ, 0<C ∧ ∀ (q : ℕ) (g : Dates→ℝ) (_ : Tendsto g (trail.curry U) (𝓝 0))
      (T : Dates→Change G d) (_ : Tendsto (fun w=>guide G d (T w)) (trail.curry U) (𝓝 0)),
      ∀ᶠ w : Dates in trail.curry U, ∀ (rp : 0<w.1) (φ : Test 3) (k : ℕ),
      let A := old F J d φ rp
      let W := film Z R d φ w.1 (s w.1) w.2.2 k (g w)
      let Q := funded Z (board R (s w.1) w.1 w.2.2) d q (g w)
      ‖old F (WilsonPositionPrescribedFrame.positioned F J Z.store) d φ rp v-W v‖ ≤
        C*(‖rows A-rows (moved (T w) W)‖+
          ‖docket (Z.store.survey d) (fun _:Unit=>hierarchy F J d w.1)-
            docket (Z.store.survey d) (retag (fun _:Unit=>T w) (fun _:Unit=>Q))‖*
          ‖rows (moved (T w) W)‖) := by
  let m := fun w : Dates=>board R (s w.1) w.1 w.2.2
  have dates : Tendsto m (trail.curry U) Front := WilsonSeparatedOriginalThermometerDetectorMesh.reporting
    R trail o U prior s _ (WilsonMaxwellThermometerPublicStation.granted R s) small
  obtain ⟨C,cp,sale⟩ := WilsonPhysicalCommonSignedAperture.original
    (Z.store.survey d) (Z.store.prepared d) (fun _:Fin 3=>()) v (trail.curry U)
  refine ⟨C,cp,?_⟩
  intro q g cold T near
  let Q := fun w : Dates=>funded Z (m w) d q (g w)
  have paid := sale (fun w (_:Unit)=>hierarchy F J d w.1) (fun w (_:Unit)=>Q w) (fun w (_:Unit)=>T w)
    (fun _=>(WilsonPositionPrescribedScreen.warm F J lead Z.store d).comp (calendar U))
    (fun _=>WilsonPositionProgramTrialPublicJointPivotMeshGauge.warm Z M H ν _ m dates d q g cold)
    (fun _=>near)
  have still := WilsonPositionProgramTrialPublicJointPivotMeshGauge.original R Z M H ν o U prior s small g cold d q
  have live := (calendar U).eventually (WilsonPositionPrescribedScreen.original F J lead Z.store d).2
  filter_upwards [paid,still,live] with w licensed ready frame
  intro rp φ k
  let W := film Z R d φ w.1 (s w.1) w.2.2 k (g w)
  have eq : positioned (Z.store.survey d) (Z.store.prepared d) (fun _:Fin 3=>()) v (fun _:Unit=>Q w) W=W v := by
    change W (fun i=>stand ((Z.store.survey d).firstPass (Z.store.prepared d) (Q w)) (v i))=W v
    rw [show (Z.store.survey d).firstPass (Z.store.prepared d) (Q w)=0 from ready.2.1,stand0]
    rfl
  have grant := licensed (old F J d φ rp) W
  rw [WilsonPositionProgramTrialPublicJointPivotEvidence.actual F J Z φ rp v frame.2.1,eq] at grant
  exact grant

end YM.Integration.WilsonPositionProgramTrialPublicJointPivotMeshSlice
