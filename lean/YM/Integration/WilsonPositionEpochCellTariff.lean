import YM.Integration.WilsonPositionOriginalEpochQuadrature

/-! Explicit joint test sampling rate for the actual independent finite torus. The field
amplitude only needs a bound on tuples touching the compact test's cells. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionEpochCellTariff
open Filter Set Finset Function Metric MeasureTheory Lattice Maxwell XSpace XSpace.Cirrus XSpace.TestBudget
open scoped Topology BigOperators Classical
variable {n : ℕ} (m : Mesh) (φ : Test n) (A : m.Tuple (n:=n) → ℂ) (c : Four ℝ)

def sampled : ℂ := (m.spacing:ℂ)^(4*n)*∑ x,φ (m.rel (m.back x) c)*A x

/-- Keep the very same finite array and integrate the test at its true position in each cell. -/
def submitted : ℂ := φ.applyTo (m.levels c A)

theorem difference {D b w : ℝ} (spacing : m.spacing ≤ 1) (wallet : Bound φ b) (hw : 0≤w)
    (radius : ∀ x∈tsupport φ,‖x‖≤D)
    (price : ∀ u:m.Tuple (n:=n), (∃ x∈m.cell c (m.back u),
      m.rel (m.back u) c∈tsupport φ ∨ x∈tsupport φ) → ‖A u‖≤w) :
    ‖sampled m φ A c-submitted m φ A c‖ ≤
      b*((4*n:ℝ)*w)*m.spacing*volume.real (closedBall (0:Points n) (D+4*n)) := by
  let Q (z:Points n) := m.levels c (fun x=>φ (m.rel (m.back x) c)*A x) z
  let E (z:Points n) := φ z*m.levels c A z
  let W := closedBall (0:Points n) (D+4*n)
  let K := b*((4*n:ℝ)*w)*m.spacing
  have hb := bound_nonneg φ wallet
  have pos := m.positive
  have hK : 0≤K := by dsimp [K]; positivity
  have zero (x : Points n) (h : x∉tsupport φ) : φ x=0 := image_eq_zero_of_notMem_tsupport h
  have edge (x y:Points n) : ‖φ x-φ y‖ ≤ b*dist x y := by
    rw [dist_eq_norm]
    exact (convex_univ (𝕜:=ℝ)).norm_image_sub_le_of_norm_fderiv_le
      (fun _ _=>φ.contDiff.differentiable (by simp) _) (fun i _=>(wallet i).2) (mem_univ y) (mem_univ x)
  have spatial (z : Points n) : ‖Q z-E z‖≤K ∧ (z∉W → Q z-E z=0) := by
    by_cases located : ∃ x:m.Tuple (n:=n),z∈m.cell c (m.back x)
    · obtain ⟨u,hu⟩ := located
      let y:=m.rel (m.back u) c
      have hQ : Q z=φ y*A u := m.stair_at c z hu
      have hE : E z=φ z*A u := by change φ z*m.levels c A z=_;rw [m.stair_at c z hu]
      rw [hQ,hE,←sub_mul]
      have near : dist y z ≤ (4*n:ℝ)*m.spacing := m.upper_corner c hu
      have used : y∈tsupport φ ∨ z∈tsupport φ → z∈W := by
        intro one
        rw [mem_closedBall,dist_zero_right]
        rcases one with hx | hz
        · exact Mesh.norm_near spacing (radius y hx) ((dist_comm z y).trans_le near)
        · exact (radius z hz).trans (le_add_of_nonneg_right (by positivity))
      by_cases hs : y∈tsupport φ ∨ z∈tsupport φ
      · refine ⟨?_,fun miss=>(miss (used hs)).elim⟩
        rw [norm_mul]
        have hr := price u ⟨z,hu,hs⟩
        calc
          _ ≤ (b*((4*n:ℝ)*m.spacing))*w := mul_le_mul
              ((edge y z).trans (mul_le_mul_of_nonneg_left near hb)) hr (norm_nonneg _) (by positivity)
          _ = _ := by dsimp [K];ring
      · rw [zero y (fun h=>hs (Or.inl h)),zero z (fun h=>hs (Or.inr h)),sub_self,zero_mul,norm_zero]
        exact ⟨hK,fun _=>rfl⟩
    · have out : ∀ u:m.Tuple (n:=n),z∉m.cell c (m.back u) := fun u hu=>located ⟨u,hu⟩
      change ‖m.levels c _ z - φ z*m.levels c A z‖≤K ∧ _
      have hQ : Q z=0 := m.stair_off c z out
      have hE : E z=0 := by change φ z*m.levels c A z=_;rw [m.stair_off c z out,mul_zero]
      change ‖Q z-E z‖≤K ∧ _
      rw [hQ,hE,sub_self,norm_zero]
      exact ⟨hK,fun _=>rfl⟩
  have eI : Integrable E := (m.integrable_stair c A).bdd_mul φ.continuous.aestronglyMeasurable
    (Eventually.of_forall fun z=>(wallet z).1)
  have qI : Integrable Q := m.integrable_stair c _
  change ‖(m.spacing:ℂ)^(4*n)*∑ x,φ (m.rel (m.back x) c)*A x - (∫ z,E z)‖ ≤ K*volume.real W
  rw [←m.stair_exact c (fun x=>φ (m.rel (m.back x) c)*A x)]
  change ‖(∫ z,Q z)-(∫ z,E z)‖ ≤ _
  rw [←integral_sub qI eI,←setIntegral_eq_integral_of_forall_compl_eq_zero (s:=W) (fun z=> (spatial z).2)]
  exact norm_setIntegral_le_of_norm_le_const (isCompact_closedBall ..|>.measure_lt_top) (fun z _=>(spatial z).1)

open FVA2 FVA2.Register FVA2.Scale XSpace.Structure1 XSpace.Normalize WilsonPositionOriginalEpochQuadrature
variable {G : Gauge} {Z : WilsonPrescription G} {i B : ℕ} (P : Handoff.Directory Z i B)
    (d q : ℕ) (v : Tags G d n) (u value : ℂ)
local notation "M" => (Z.run.step i)

def data (x : (M).Tuple (n:=n)) : ℂ :=
  ∑ k∈range (q+1),point P d v ((M).back x) k * u^k

/-- A bound on the submitted actual cell integrals on the same finite program pays the
manuscript's compact signed raw report, up to one spatial sampling error. -/
theorem original {D b w ε : ℝ} (spacing : (M).spacing ≤ 1) (wallet : Bound φ b) (hw : 0≤w)
    (radius : ∀ x∈tsupport φ,‖x‖≤D)
    (width : ∀ c∈(M).Box,∀ x:(M).Tuple (n:=n),(∃ y∈(M).cell c ((M).back x),
      (M).rel ((M).back x) c∈tsupport φ ∨ y∈tsupport φ) → ‖data P d q v u x‖≤w)
    (heard : ∀ c∈(M).Box, ‖submitted M φ (data P d q v u) c-value‖≤ε) :
    ‖(∑ k∈range (q+1),WilsonPositionRawEpoch.row Z P d φ v k*u^k)-value‖ ≤
      b*((4*n:ℝ)*w)*(M).spacing*volume.real (closedBall (0:Points n) (D+4*n)) + ε := by
  let Y (s : Sample n) := ∑ k∈range (q+1),point P d v s.layout k*u^k
  rw [whole P d φ v q u]
  change ‖Deposit M Y φ-value‖ ≤ _
  apply homeward_price M φ Y value _
  intro c hc
  rw [stroll]
  change ‖sampled M φ (data P d q v u) c-value‖ ≤ _
  have sample := difference M φ (data P d q v u) c spacing wallet hw radius (width c hc)
  calc
    _ ≤ ‖sampled M φ (data P d q v u) c - submitted M φ (data P d q v u) c‖ +
        ‖submitted M φ (data P d q v u) c-value‖ := by simpa only [dist_eq_norm] using dist_triangle (sampled M φ (data P d q v u) c) (submitted M φ (data P d q v u) c) value
    _ ≤ _ := add_le_add sample (heard c hc)

end YM.Integration.WilsonPositionEpochCellTariff
