import YM.Integration.WilsonThermometerOwnOffsetWeakRows
import YM.Integration.WilsonPositionPhysicalCellTest

/-! Exact finite-cell integration of the displaced physical weak detector.
All positions and filed source coordinates are allowed to vary cell by cell.
The whole (Stock.census (Fin 2)) is pushed through the same original vacuum before a face is read. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonAddressedWeakPointCells
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source RG12 Extra.Histories
open RG05Readout Native Address Many Records Harvest Push.GridApprox Copper Push Marker
open PhysicalNext.Repeat.Legato MergeProof Accent Motion Bandage Extra.Multi Menu
open Next.Rank Edition Baler Value Glyph Thirst Alarm Extraction Table Spec
open Cells XSpace.Structure1
open OPE OPE.Orbits PhysMS XSpace XSpace.Normalize Trace Trace.Pilot
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetResidue WilsonThermometerOwnOffsetField
open scoped Classical BigOperators Topology
abbrev PointSites {G : Gauge} (R : Run G) (N p : ℕ) := Fin 2 → Site (R.family.side N p)

variable {G : Gauge} (R : Run G) {N p k : ℕ} (d : Fin 2 → ℕ)
variable (o : (PointSites R N p)) (y : (i : Fin 2) → Palette R.family (d i))
  (r : (i : Fin 2) → Emblems R.family (d i)) (live : k ≤ N)

section Cells
open WilsonPositionPhysicalCellTest
variable {n : ℕ} {R : Run G} (r : ℝ) (z : UVIndex)
private theorem visible (u : WilsonPositionPhysicalCellTest.Sites R z n) : MeasurableSet (cell r z u) := by
  have grid : Measurable (address (R.family.S.a z.1) : Points n → Fin n → Cover) := by
    apply measurable_to_countable
    intro x
    exact measurable_segment (R.family.S.a_pos z.1) (address (R.family.S.a z.1) x)
  let U : Set (Fin n → Cover) := {c | wrap _ ∘ c=u}
  exact (Set.to_countable U).measurableSet.preimage (grid.comp (continuous_const_smul r).measurable)

private theorem integrate {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : WilsonPositionPhysicalCellTest.Sites R z n → Points n → E) (finite : ∀ u, Integrable (h u)) :
    (∫ x, h (site r z x) x) = ∑ u, ∫ x in cell r z u, h u x := by
  have partition (x : Points n) : h (site r z x) x = ∑ u, (cell r z u).indicator (h u) x := by
    simp [Set.indicator_apply,cell]
  have paid (u : WilsonPositionPhysicalCellTest.Sites R z n) := (finite u).indicator (visible r z u)
  simp_rw [partition]
  rw [integral_finsetSum _ (fun u _=>paid u)]
  exact Finset.sum_congr rfl fun u _=>integral_indicator (visible r z u) ..

end Cells

def reading (face : (Stock.census (Fin 2)).Mode) : ℂ :=
  (∫ U : Config G (R.family.side k p), WilsonThermometerIntrinsicRoster.density R d o y r (Stock.census (Fin 2)) live live U ∂prior G _).part face /
    (partition G (R.family.side N p) (R.family.beta N p) : ℂ)

theorem conserved (face : (Stock.census (Fin 2)).Mode) :
    reading R d o y r live face =
    (∫ U, Accent.birth (Stock.census (Fin 2)) (R.family.path.rep N p N)
      (WilsonThermometerIntrinsicRoster.source R d o y r live) U ∂prior G _).part face /
        (partition G (R.family.side N p) (R.family.beta N p) : ℂ) := by
  let joint := WilsonThermometerIntrinsicRoster.source R d o y r live
  have hc (i : Fin 2) : Continuous (joint i) := by
    change Continuous (fun U => (R.family.S.a k:ℂ)^(d i) • R.family.O N p _ (o i) U)
    exact (R.family.continuousO N p (d i) _ (o i)).const_smul ((R.family.S.a k:ℂ)^(d i))
  have hv : Continuous (R.family.path.rep N p N).eval := by
    rw [(show (R.family.path.rep N p N).eval = _ from (R.makes.wilson.starts N p).2)]
    exact bare_cont _
  have ht : Integrable (Accent.birth (Stock.census (Fin 2)) (R.family.path.rep N p N) joint) (prior G _) := (hatCont R.family N p joint hc hv (Stock.census (Fin 2))).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  unfold reading WilsonThermometerIntrinsicRoster.density
  rw [gust_sum _ _ _ _ _ ht]

variable (Y : (PointSites R N p) → (i : Fin 2) → Palette R.family (d i))
  (U : (PointSites R N p) → (i : Fin 2) → Emblems R.family (d i))

def matrixEntry (φ : Test 2) (a : ℝ) (face : (Stock.census (Fin 2)).Mode) : ℂ :=
  ∑ o : (PointSites R N p), WilsonPositionPhysicalCellTest.mass φ a (N,p) o *
    reading R d o (Y o) (U o) live face

theorem integrated (φ : Test 2) (a : ℝ) (face : (Stock.census (Fin 2)).Mode) :
    matrixEntry R d live Y U φ a face =
      ∫ x, φ x * reading R d (WilsonPositionPhysicalCellTest.site a (N,p) x)
        (Y (WilsonPositionPhysicalCellTest.site a (N,p) x))
        (U (WilsonPositionPhysicalCellTest.site a (N,p) x)) live face := by
  let q := fun o : (PointSites R N p) => reading R d o (Y o) (U o) live face
  have hi (o : (PointSites R N p)) : Integrable (fun x => φ x * q o) :=
    (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).mul_const (q o)
  rw [integrate a (N,p) (fun o x => φ x * q o) hi]
  simp only [matrixEntry,WilsonPositionPhysicalCellTest.mass,integral_mul_const,q]

theorem charged (φ : Test 2) (a : ℝ) (face : (Stock.census (Fin 2)).Mode) (target : Points 2 → ℂ)
    (δ : ℝ) (hδ : 0 ≤ δ) (ht : Integrable (fun x => φ x * target x))
    (atPoints : ∀ x, φ x ≠ 0 →
      ‖reading R d (WilsonPositionPhysicalCellTest.site a (N,p) x)
        (Y (WilsonPositionPhysicalCellTest.site a (N,p) x))
        (U (WilsonPositionPhysicalCellTest.site a (N,p) x)) live face - target x‖ ≤ δ) :
    ‖matrixEntry R d live Y U φ a face - ∫ x, φ x * target x‖ ≤
      (∫ x, ‖φ x‖) * δ := by
  let q := fun o : (PointSites R N p) => reading R d o (Y o) (U o) live face
  let o := WilsonPositionPhysicalCellTest.site (R:=R) (n:=2) a (N,p)
  have hφ : Integrable (fun x : Points 2 => φ x) := φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  have legal (u : (PointSites R N p)) : Integrable (fun x => φ x * q u) := hφ.mul_const _
  have hq : Integrable (fun x => φ x * q (o x)) := by
    have tab (x : Points 2) : φ x * q (o x) =
        ∑ u : (PointSites R N p), (WilsonPositionPhysicalCellTest.cell (R:=R) a (N,p) u).indicator (fun v => φ v * q u) x := by
      simp [WilsonPositionPhysicalCellTest.cell,Set.indicator_apply,o]
    simp_rw [tab]
    apply integrable_finsetSum
    intro u _
    exact (legal u).indicator (visible a (N,p) u)
  rw [integrated]
  change ‖(∫ x, φ x * q (o x)) - ∫ x, φ x * target x‖ ≤ _
  rw [←integral_sub hq ht,←integral_mul_const]
  refine (norm_integral_le_integral_norm _).trans ?_
  apply integral_mono (hq.sub ht).norm (hφ.norm.mul_const δ)
  intro x
  change ‖φ x * q (o x) - φ x * target x‖ ≤ ‖φ x‖ * δ
  by_cases hz : φ x = 0
  · simpa only [hz,zero_mul,sub_self,norm_zero] using (mul_nonneg (norm_nonneg (φ x)) hδ)
  · rw [←mul_sub,norm_mul]
    exact mul_le_mul_of_nonneg_left (atPoints x hz) (norm_nonneg _)

end YM.Integration.WilsonAddressedWeakPointCells
