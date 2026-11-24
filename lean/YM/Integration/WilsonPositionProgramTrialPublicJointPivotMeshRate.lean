import YM.Integration.WilsonPositionProgramTrialPublicJointPivotMeshCells

/-! Thermal valuation of the signed coefficient remainder on the original physical cells. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionProgramTrialPublicJointPivotMeshRate
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
open scoped Classical BigOperators Topology
variable {G : Gauge} (R : Run G) (Z : WilsonPrescription G) {hG : G.Simple}
  (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) {σ : Prescription (Press.portDeck G)}
  {dial : Bool} (H : Main.Match Z hG M σ dial) (ν : ℝ)


abbrev Dates := ℝ×(ℕ×ℕ)
variable (s : ℝ→ℕ) {d : ℕ} (φ : Dates → Test 3) (p : Dates → Fin 3 → Sec G d)

def residual (k : ℕ) (w : Dates) : ℂ :=
  panel R Z d (φ w) w.1 (s w.1) (s w.1,w.2.2) le_rfl k (p w) - limit Z M H ν d (φ w) k (p w)

def wage (w : Dates) : ℝ := (∏ i,salary (p w i))*(∫ x,‖φ w x‖)

theorem coefficient (o : Extraction.Order) (U : Filter (ℕ×ℕ)) (prior : U≤o.fuse)
    (small : Tendsto (aperture R s) trail (𝓝 0)) (K : Set (Points 3)) (hc : IsCompact K) (hs : K ⊆ conf 3)
    (supported : ∀ᶠ w in trail.curry U,tsupport (φ w) ⊆ K) {B : ℝ} (pos : 0≤B)
    (income : ∀ᶠ w in trail.curry U,wage φ p w ≤ B) (k : ℕ) :
    Tendsto (residual R Z M H ν s φ p k) (trail.curry U) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε ep
  let η := ε/(B+1)
  have pay : 0<η := div_pos ep (by linarith)
  filter_upwards [WilsonPositionProgramTrialPublicJointPivotMeshCells.original R Z M H ν o U prior s small d k K hc hs pay,
    income,supported] with w date bought contained
  simp only [dist_zero_right]
  have cap := date (s w.1) le_rfl ⟨k,Nat.lt_succ_self _⟩ (φ w) contained (p w)
  calc
    ‖residual R Z M H ν s φ p k w‖ ≤ wage φ p w*η := by simpa only [residual,wage,mul_assoc] using cap
    _ ≤ B*η := mul_le_mul_of_nonneg_right bought pay.le
    _ < (B+1)*η := mul_lt_mul_of_pos_right (by linarith) pay
    _ = ε := by dsimp [η];field_simp

theorem original (o : Extraction.Order) (U : Filter (ℕ×ℕ)) (prior : U≤o.fuse)
    (small : Tendsto (aperture R s) trail (𝓝 0)) (K : Set (Points 3)) (hc : IsCompact K) (hs : K ⊆ conf 3)
    (supported : ∀ᶠ w in trail.curry U,tsupport (φ w) ⊆ K) {B : ℝ} (pos : 0≤B)
    (income : ∀ᶠ w in trail.curry U,wage φ p w ≤ B) (t : Dates→ℂ)
    (cold : Tendsto t (trail.curry U) (𝓝 0)) (live : ∀ᶠ w in trail.curry U,t w≠0) (a q : ℕ) :
    Tendsto (fun w=>(∑ k∈Icc a q,t w^k*residual R Z M H ν s φ p k w)/t w^a)
      (trail.curry U) (𝓝 0) := by
  have tail : Tendsto (fun w=>∑ k∈Icc a q,t w^(k-a)*residual R Z M H ν s φ p k w)
      (trail.curry U) (𝓝 0) := by
    simpa only [mul_zero,Finset.sum_const_zero] using tendsto_finsetSum (Icc a q)
      (fun k _=>(cold.pow (k-a)).mul (coefficient R Z M H ν s φ p o U prior small K hc hs supported pos income k))
  apply tail.congr'
  filter_upwards [live] with w hot
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun k hk=>?_
  apply (eq_div_iff (pow_ne_zero a hot)).2
  calc
    _ = (t w^(k-a)*t w^a)*residual R Z M H ν s φ p k w := by ring
    _ = _ := by rw [←pow_add,Nat.sub_add_cancel (mem_Icc.mp hk).1]

end YM.Integration.WilsonPositionProgramTrialPublicJointPivotMeshRate
