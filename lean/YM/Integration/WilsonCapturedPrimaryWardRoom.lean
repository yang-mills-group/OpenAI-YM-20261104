import YM.Integration.WilsonCapturedPrimaryWardFile
import YM.Integration.WilsonCapturedPrimaryPhysicalChamber
import YM.Integration.WilsonSeparatedOffsetSites

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryWardRoom
open Function Set Filter Finset MeasureTheory Lattice Wilson RG Labels Source Push
open Extraction MergeProof MergeProof.Ribbons Extra.Histories Cells
open scoped Classical Topology BigOperators
variable {G : Gauge} {n : Side} (C : Family G)

theorem ball (T : Tiling n) {k : ℕ} {o z : Site n}
    (inner : o ∈ T.margin 0 k) (near : separation z o < k) : z ∈ T.chamber 0 := by
  have bound (a : Axis) : (lift (z-o) a).natAbs < k :=
    (component_le (z-o) a).trans_lt near
  simpa using T.fits_stencil inner bound

/-- Every named chart footprint and the entire Ward exclusion ball are in the base chamber. -/
theorem original (J radius d : ℕ) (V : SectionData (C.labels.level d)) :
    ∀ᶠ N : ℕ in atTop, ∀ (h : J ≤ N) (p : ℕ) (o : Site (C.side N p)),
    8*‖C.S.place o‖ ≤ C.S.a J → let T := center C.S p h 0
    (T.chamber 0)ᶜ ⊆ Mark.Outer radius o ∧
      (↑(V.footprint o) : Set _) ⊆ T.chamber 0 := by
  obtain ⟨L,all⟩ := WilsonSeparatedOffsetSites.footprint (C:=C) V
  let K := max L radius+1
  have shrink := C.S.shrinks.mul_const ((8*K : ℕ) : ℝ)
  rw [zero_mul] at shrink
  filter_upwards [all,shrink.eventually (ge_mem_nhds (C.S.a_pos J))] with N localV small
  intro h p o charge
  let T := center C.S p h 0
  have fees : C.S.a N * (↑(8*K : ℕ) : ℝ) ≤ C.S.a N * T.side.val :=
    small.trans_eq (C.S.embeds_scale T.units).symm
  have fit : 8*K ≤ T.side.val := by exact_mod_cast le_of_mul_le_mul_left fees (C.S.a_pos N)
  have inner := lat_inside C J p N h o charge
  have radius_lt : radius < T.side.val/8 := by dsimp [K] at fit; omega
  have size_lt : L < T.side.val/8 := by dsimp [K] at fit; omega
  constructor
  · intro x outside
    change radius < separation x o
    by_contra! contained
    exact outside (ball T inner (contained.trans_lt radius_lt))
  · intro x member
    exact ball T inner ((localV p o x member).trans_lt size_lt)

end YM.Integration.WilsonCapturedPrimaryWardRoom
