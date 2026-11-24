import YM.Integration.WilsonPositionProgramTrialPublicJointPivotMeshAddress
import YM.Integration.WilsonMaxwellThermometerFirstCells

/-! The finite timed rose uses the original signed physical cell masses at both the parent and reporting dates. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionProgramTrialPublicJointPivotMeshCells
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
open private payable from YM.Integration.WilsonMaxwellThermometerFirstCells
open scoped Classical BigOperators Topology
variable {G : Gauge} (R : Run G) (Z : WilsonPrescription G) {hG : G.Simple}
  (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) {σ : Prescription (Press.portDeck G)}
  {dial : Bool} (H : Main.Match Z hG M σ dial) (ν : ℝ)

def panel (d : ℕ) (φ : Test 3) (r : ℝ) (f : ℕ) (z : ℕ×ℕ) (live : f≤z.1) (k : ℕ) : Row G d 3 :=
  ∑ y : locations R z,WilsonCenteredCompactBooking.mass R φ r z y •
    mark (Rose.measureₓ Z.scheme Z.criterion d (lowerSite R f r z live y)) k

theorem tested (d : ℕ) (φ : Test 3) (r : ℝ) (f : ℕ) (z : ℕ×ℕ) (live : f≤z.1) (k : ℕ) (p : Fin 3→Sec G d) :
    panel R Z d φ r f z live k p = φ.applyTo (fun x=>coeff k (signed
      (Rose.measureₓ Z.scheme Z.criterion d (lowerSite R f r z live (positions (R:=R) r z x))) p)) := by
  have same (y : locations R z) : weight φ (positions (R:=R) r z) y=WilsonCenteredCompactBooking.mass R φ r z y :=
    integral_indicator ((measurableSet_singleton y).preimage (placed (R:=R) r z))
  rw [WilsonSeparatedOriginalThermometerCells.tested φ _ (placed (R:=R) r z) (fun y=>coeff k (signed (Rose.measureₓ Z.scheme Z.criterion d (lowerSite R f r z live y)) p))]
  simp only [panel,_root_.sum_apply,_root_.smul_apply,smul_eq_mul,same]
  rfl

theorem occupied (d : ℕ) (φ : Test 3) (r : ℝ) (f per k : ℕ) (p : Fin 3→Sec G d) :
    panel R Z d φ r f (f,per) le_rfl k p = WilsonReceivedChronologicalFixedRoseVariation.signed R φ r (f,per)
      (fun y=>coeff k (signed (Rose.measureₓ Z.scheme Z.criterion d
        (WilsonOriginalObservedRoseBornAbsolute.cell R φ r f per y)) p)) := by
  let μ := WilsonCenteredCompactBooking.mass R φ r (f,per)
  let t := fun y : locations R (f,per) => coeff k (signed (Rose.measureₓ Z.scheme Z.criterion d
    (lowerSite R f r (f,per) le_rfl y)) p)
  change _ = ∑ y : cells R φ r (f,per), μ y.val*t y.val
  rw [show (∑ y : cells R φ r (f,per), μ y.val*t y.val) = ∑ y∈cells R φ r (f,per),μ y*t y by
    simpa only [attach_eq_univ] using sum_attach (cells R φ r (f,per)) (fun y=>μ y*t y)]
  simp only [panel,_root_.sum_apply,_root_.smul_apply,smul_eq_mul]
  change ∑ y,μ y*t y = _
  apply (sum_subset (subset_univ _) ?_).symm
  intro y _ missing
  have zero : μ y=0 := by
    by_contra nh
    exact missing (mem_filter.mpr ⟨mem_univ _,nh⟩)
  rw [zero,zero_mul]

theorem compact (o : Extraction.Order) (U : Filter (ℕ×ℕ)) (prior : U≤o.fuse) (s : ℝ→ℕ)
    (small : Tendsto (aperture R s) trail (𝓝 0)) (d k : ℕ) (p : Fin 3→Sec G d) (K : Set (Points 3))
    (hc : IsCompact K) (hs : K ⊆ conf 3) {ε : ℝ} (ep : 0<ε) :
    ∀ᶠ w : ℝ×(ℕ×ℕ) in trail.curry U, ∀ (N : ℕ) (live : s w.1≤N), ∀ φ : Test 3, tsupport φ ⊆ K →
      ‖panel R Z d φ w.1 (s w.1) (N,w.2.2) live k p - limit Z M H ν d φ k p‖ ≤ (∫ x,‖φ x‖)*ε := by
  filter_upwards [WilsonPositionProgramTrialPublicJointPivotMeshAddress.original Z M H ν R o U prior s small d k p K hc hs ep] with w date
  intro N live φ support
  let r := w.1
  let z := (N,w.2.2)
  let site := positions (R:=R) r z
  let Y := fun y : locations R z => coeff k (signed (Rose.measureₓ Z.scheme Z.criterion d
    (lowerSite R (s r) r z live y)) p)
  let F := fun x => coeff k (signed (Jury.fxt (Measure.start Z.scheme Z.criterion d) x) p)
  rw [tested]
  change ‖(∫ x,φ x*Y (site x))-(∫ x,φ x*F x)‖≤_
  have target : Integrable (fun x=>φ x*F x) := Cirrus.can_pay φ F (conf_open _) (measured Z M H ν d k p).priced φ.tsupport_subset (Subset.refl _)
  rw [←integral_sub (payable site (placed (R:=R) r z) φ Y) target]
  have test : Integrable (fun x : Points 3=>φ x) := φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  refine (norm_integral_le_of_norm_le (test.norm.mul_const ε) (Eventually.of_forall fun x=>?_)).trans_eq (integral_mul_const ..)
  rw [←mul_sub,norm_mul]
  by_cases hx : x∈tsupport φ
  · exact mul_le_mul_of_nonneg_left (date N live x (support hx)) (norm_nonneg _)
  · simp only [image_eq_zero_of_notMem_tsupport hx,norm_zero,zero_mul,le_rfl]

theorem original (o : Extraction.Order) (U : Filter (ℕ×ℕ)) (prior : U≤o.fuse) (s : ℝ→ℕ)
    (small : Tendsto (aperture R s) trail (𝓝 0)) (d q : ℕ) (K : Set (Points 3))
    (hc : IsCompact K) (hs : K ⊆ conf 3) {ε : ℝ} (ep : 0<ε) :
    ∀ᶠ w : ℝ×(ℕ×ℕ) in trail.curry U, ∀ (N : ℕ) (live : s w.1≤N), ∀ (k : Fin (q+1)) (φ : Test 3),
      tsupport φ ⊆ K → ∀ p : Fin 3→Sec G d,
      ‖panel R Z d φ w.1 (s w.1) (N,w.2.2) live k p - limit Z M H ν d φ k p‖ ≤
        (∏ j,salary (p j))*((∫ x,‖φ x‖)*ε) := by
  have dates (k : Fin (q+1)) (b : Fin 3 → Pin G d) :=
    compact R Z M H ν o U prior s small d k (fun j=>Module.finBasis ℝ (Sec G d) (b j)) K hc hs ep
  filter_upwards [Filter.eventually_all.mpr (fun k=>Filter.eventually_all.mpr (dates k))] with w window
  intro N live k φ support p
  exact paid _ _ p (mul_nonneg (integral_nonneg (fun _=>norm_nonneg _)) ep.le) (fun b=>window k b N live φ support)

end YM.Integration.WilsonPositionProgramTrialPublicJointPivotMeshCells
