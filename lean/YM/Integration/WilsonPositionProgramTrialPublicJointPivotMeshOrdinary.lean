import YM.Integration.WilsonPositionProgramTrialPublicJointPivotMeshAddress

/-! The ordinary signed pivot table runs on the actual finite group chart at every arity and horizon. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionProgramTrialPublicJointPivotMeshOrdinary
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
open WilsonMaxwellThermometerSignedWallet (board)
open scoped Classical BigOperators Topology
variable {G : Gauge} (R : Run G) (Z : WilsonPrescription G) {hG : G.Simple}
  (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) {σ : Prescription (Press.portDeck G)}
  {dial : Bool} (H : Main.Match Z hG M σ dial) (ν : ℝ)


include H in
theorem compact (d k n : ℕ) (p : Fin n → Sec G d) (K : Set (Points n)) (hc : IsCompact K) (hs : K ⊆ conf n)
    {ε : ℝ} (ep : 0<ε) : ∀ᶠ m in Front, ∀ φ : Test n, tsupport φ ⊆ K → ∀ B : ℝ, TestBudget.Bound φ B →
      ‖Rose.proposed Z.scheme Z.criterion m d k n φ p - Reg.Faith.reports ν Z.criterion M d k n φ p‖ ≤ B*ε := by
  simp_rw [Rose.represents,WilsonPositionProgramTrialPublicJointPivotForecast.prescribed Z M H ν]
  exact graduate _ _ (conf_open n) (senses Z M H ν d n k p).priced hs hc (senses Z M H ν d n k p)
    (fun _ _ _=>rfl) ε ep

include H in
theorem mesh (d q n : ℕ) (K : Set (Points n)) (hc : IsCompact K) (hs : K ⊆ conf n) {ε : ℝ} (ep : 0<ε) :
    ∀ᶠ m in Front, ∀ (k : Fin (q+1)) (φ : Test n), tsupport φ ⊆ K → ∀ B : ℝ, TestBudget.Bound φ B →
      ∀ p : Fin n → Sec G d,
      ‖Rose.proposed Z.scheme Z.criterion m d k n φ p - Reg.Faith.reports ν Z.criterion M d k n φ p‖ ≤
        (∏ j,salary (p j))*(B*ε) := by
  have dates (k : Fin (q+1)) (b : Fin n → Pin G d) :=
    compact Z M H ν d k n (fun j=>Module.finBasis ℝ (Sec G d) (b j)) K hc hs ep
  filter_upwards [Filter.eventually_all.mpr (fun k=>Filter.eventually_all.mpr (dates k))] with m window
  intro k φ supported B bounded p
  exact paid (Rose.proposed Z.scheme Z.criterion m d k n φ) (Reg.Faith.reports ν Z.criterion M d k n φ) p
    (mul_nonneg (TestBudget.bound_nonneg φ bounded) ep.le) (fun b=>window k b φ supported B bounded)

include H in
theorem original (o : Extraction.Order) (U : Filter (ℕ×ℕ)) (prior : U≤o.fuse) (s : ℝ→ℕ)
    (small : Tendsto (aperture R s) trail (𝓝 0)) {I : Type*} [Fintype I]
    (d q n : I→ℕ) (K : ∀ i, Set (Points (n i))) (hc : ∀i,IsCompact (K i)) (hs : ∀i,K i ⊆ conf (n i))
    {ε : ℝ} (ep : 0<ε) : ∀ᶠ w : ℝ×(ℕ×ℕ) in trail.curry U,
      ∀ (i : I) (k : Fin (q i+1)) (φ : Test (n i)), tsupport φ ⊆ K i → ∀ B : ℝ, TestBudget.Bound φ B →
      ∀ p : Fin (n i) → Sec G (d i),
      ‖Rose.proposed Z.scheme Z.criterion (board R (s w.1) w.1 w.2.2) (d i) k (n i) φ p -
        Reg.Faith.reports ν Z.criterion M (d i) k (n i) φ p‖ ≤ (∏ j,salary (p j))*(B*ε) := by
  have geo := WilsonSeparatedOriginalThermometerDetectorMesh.reporting R trail o U prior s _ 
    (WilsonMaxwellThermometerPublicStation.granted R s) small
  exact geo.eventually (Filter.eventually_all.mpr fun i=>mesh Z M H ν (d i) (q i) (n i) (K i) (hc i) (hs i) ep)

end YM.Integration.WilsonPositionProgramTrialPublicJointPivotMeshOrdinary
