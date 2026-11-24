import YM.Integration.WilsonPositionProgramConvertedRun
import YM.Integration.WilsonPositionPhysicalCellTest

/-! Hear the fixed field conversion of the independent chronological program on the
actual microscopic Wilson cells, with all child coordinates independently addressed. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionProgramPhysicalCells
open Function Set Filter Finset MeasureTheory Metric Extraction Lattice Wilson RG
open PhysicalNext.Repeat.Legato RG17 Maxwell XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open FVA2 FVA2.Register FVA2.Scale MS MS.Land
open WilsonPositionProgramFixedFrame WilsonPositionPhysicalCellTest
open scoped Topology BigOperators Classical ContDiff
variable {G : Gauge} (Z : WilsonPrescription G) {hG : G.Simple}
    {M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
    {T : Prescription (Press.portDeck G)} {dial : Bool} (H : Main.Match Z hG M T dial)
    (μ : ℝ) {d n : ℕ} (v : Tags G d n) (k : ℕ)

/-- The smooth corrected coefficient used to compare nearby positions of the same source. -/
def point (x : Points n) : ℂ :=
  value Z (M:=M) μ v k (fun t j=>Dframe.meteor μ M d x j (Dframe.fill t))

private theorem smooth (x : Points n) (hx : x∈conf n) : ContDiffAt ℝ ∞ (point Z (M:=M) μ v k) x := by
  unfold point value
  apply ContDiffAt.sum
  intro a _
  apply ContDiffAt.sum
  intro j _
  apply ContDiffAt.sum
  intro s _
  exact contDiffAt_const.mul (Speed.Star.smooth_r μ M (Dframe.fill s) j x hx)

theorem shifts (K : Set (Points n)) (compact : IsCompact K) (sep : K ⊆ conf n) :
    ∃ c L : ℝ, 0<c ∧ 0≤L ∧ ∀ x∈K,∀ y∈closedBall x c,
      ‖point Z (M:=M) μ v k y-point Z (M:=M) μ v k x‖ ≤ L*dist y x := by
  obtain ⟨c,cp,collar⟩ := compact.exists_cthickening_subset_open (conf_open n) sep
  let F := point Z (M:=M) μ v k
  let D := cthickening c K
  have hc : IsCompact D := compact.cthickening
  have hs (x) (hx : x∈D) : ContDiffAt ℝ ∞ F x := smooth Z μ v k x (collar hx)
  have hd : ContinuousOn (fderiv ℝ F) D := fun x hx=>((hs x hx).continuousAt_fderiv (by simp)).continuousWithinAt
  obtain ⟨L,hL⟩ := (hc.image_of_continuousOn hd.norm).bddAbove
  refine ⟨c,max L 0,cp,le_max_right ..,?_⟩
  intro x hx y hy
  have holds : closedBall x c ⊆ D := fun z hz=>mem_cthickening_of_dist_le z x c K hx hz
  rw [dist_eq_norm]
  exact (convex_closedBall x c).norm_image_sub_le_of_norm_fderiv_le
    (fun z hz=>(hs z (holds hz)).differentiableAt (by simp))
    (fun z hz=>(hL (mem_image_of_mem _ (holds hz))).trans (le_max_left ..)) (mem_closedBall_self cp.le) hy

variable {R : Run G} (φ : Test n) (r : ℝ) (z : ℕ × ℕ)

private theorem blocks : Measurable (site (R:=R) r z (n:=n)) := by
  have grid : Measurable (address (R.family.S.a z.1) : Points n → Fin n → Cover) := by
    apply measurable_to_countable
    intro x
    exact measurable_segment (R.family.S.a_pos z.1) (address (R.family.S.a z.1) x)
  exact Measurable.of_discrete.comp (grid.comp (continuous_const_smul r).measurable)

private theorem test_values (g : Sites R z n → ℂ) :
    φ.applyTo (fun x=>g (site r z x)) = ∑ u, mass φ r z u*g u := by
  have mh (u:Sites R z n) : MeasurableSet (cell r z u) := (measurableSet_singleton u).preimage (blocks r z)
  have mp : Integrable (φ : Points n → ℂ) volume := φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  have partition (x:Points n) : ∑ u:Sites R z n,(cell r z u).indicator (fun y=>φ y*g u) x=φ x*g (site r z x) := by
    classical
    simp [cell,Set.indicator_apply]
  unfold Test.applyTo
  simp_rw [←partition]
  rw [integral_finsetSum _ (fun u _=>(mp.mul_const _).indicator (mh u))]
  exact sum_congr rfl fun u _=>by rw [integral_indicator (mh u),integral_mul_const];rfl

include H in
/-- A uniform error on the signed chronological coefficient is integrated against the
full joint test, incurring just its L¹ norm on the original cutoff. -/
theorem measured (g : Sites R z n → ℂ) (E : ℝ)
    (heard : ∀ y∈tsupport φ, ‖g (site r z y)-point Z (M:=M) μ v k y‖ ≤ E) :
    ‖(∑ u, mass φ r z u*g u)-WilsonPositionSeparatedProfileMatching.coefficient Z M μ d φ v k‖ ≤
        (∫ y,‖φ y‖)*E := by
  let P := point Z (M:=M) μ v k
  let V (y:Points n) := g (site r z y)
  have target := φ.smearing (show ContinuousOn P (conf n) from fun y hy=>(smooth Z μ v k y hy).continuousAt.continuousWithinAt)
  have mp : Integrable (φ : Points n → ℂ) volume := φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  have seen : WilsonPositionSeparatedProfileMatching.coefficient Z M μ d φ v k = φ.applyTo P := by
    rw [WilsonPositionSeparatedProfileMatching.filed Z M H]
    apply φ.apply_eq
    intro y hy
    simp only [WilsonPositionSeparatedProfileMatching.extended,dif_pos hy]
    exact (output Z H μ v k ⟨y,hy⟩).symm
  have assigned : Measurable V := Measurable.of_discrete.comp (blocks r z)
  have bound (y : Points n) : ‖φ y*V y-φ y*P y‖ ≤ ‖φ y‖*E := by
    by_cases absent : φ y=0
    · simp [absent]
    rw [←mul_sub,norm_mul]
    exact mul_le_mul_of_nonneg_left (heard y (subset_closure absent)) (norm_nonneg _)
  have measurable : AEStronglyMeasurable (fun y=>φ y*V y-φ y*P y) volume :=
    (φ.continuous.measurable.mul assigned).aestronglyMeasurable.sub target.aestronglyMeasurable
  have di := (mp.norm.mul_const E).mono' measurable (Eventually.of_forall bound)
  have vi : Integrable (fun y=>φ y*V y) := (di.add target).congr (Eventually.of_forall fun y=>sub_add_cancel _ _)
  rw [←test_values φ r z g,seen]
  change ‖(∫ y, φ y*V y)-(∫ y,φ y*P y)‖ ≤ _
  rw [←integral_sub vi target,←integral_mul_const]
  exact norm_integral_le_of_norm_le (mp.norm.mul_const E) (Eventually.of_forall bound)

end YM.Integration.WilsonPositionProgramPhysicalCells
