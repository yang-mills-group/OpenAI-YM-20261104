import YM.Integration.WilsonAddressedCollarSites
import YM.Integration.WilsonPositionThermometerJointFaces

/-! Reindex the cutoff fields themselves on the actual depth map. Both the
    period and the original configuration are the same in every summand. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonAddressedCollarFolds
open Filter MeasureTheory Lattice Wilson RG Source Extraction Table Spec
open RG05Readout RG05Readout.Address RG05Readout.Pulse
open RG05Readout.Native RG05Readout.Records RG05Readout.Flatten
open Trace.Pilot OPE OPE.Orbits Climb RG12 PhysicalNext.Repeat.Legato
open XSpace XSpace.Rose Cells Push.GridApprox
open WilsonPositionThermometerGradedSource WilsonPositionThermometerCapStation
open WilsonPositionThermometerGradedReading
open scoped Classical BigOperators Topology
variable {G : Gauge} {C : Family G} {V : Type} [Fintype V] [DecidableEq V]

private theorem census {M : Type*} [AddCommMonoid M] {w N p : ℕ} (h : w ≤ N)
    (f : (V → Site (C.side N p)) → M) :
    let cell := C.S.toDepth h p
    ∑ x, f x = ∑ parent : V → Site (C.side w p), ∑ t : V → Site cell.count,
      f (fun i => cell.assemble (parent i,t i)) := by
  let E := walks (C:=C) (p:=p) (V:=V) h 0
  rw [←Equiv.sum_comp E,Fintype.sum_prod_type]
  simp only [E,walks,Equiv.coe_fn_mk,add_zero]

/-- The complete fine field under an arbitrary smooth joint test. One keeps
    the entire residue of each child and every physically admitted test jet. -/
theorem addressed {m w N p : ℕ} (h : w ≤ N) (d : V → ℕ)
    (x : (i : V) → Palette C (d i)) (φ : Wave V) (U : Config G (C.side N p)) :
    let cell := C.S.toDepth h p
    multi C m N p d x φ U =
      (∏ i, gate C m N (d i)) *
      ∑ c : V → Site (C.side w p), ∑ t : V → Site cell.count,
      let y := fun i => cell.assemble (c i,t i)
      ∑ j : (i : V) → Mark C (d i),
        (((C.S.a N : ℂ)^pegs d (fun i => (j i).1) (Finset.univ (α:=V)).toList) *
          (perform d (fun i => (j i).1) φ).val (fun i => C.S.place (y i))) *
          ∏ i, key C N p (d i) (x i) (j i) (y i) U := by
  unfold multi
  simp only [LinearMap.smul_apply,LinearMap.sum_apply,LinearMap.comp_apply,
    Pi.smul_apply,smul_eq_mul,Finset.sum_apply]
  apply congrArg ((_ : ℂ) * ·)
  rw [census (C:=C) h]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro t _
  unfold harpoon
  apply Finset.sum_congr rfl
  intro j _
  rw [WilsonAddressedCollarSites.ray]

variable {R : Run G} (A : Group R.family 6) (r : ℝ) (z : UVIndex)
local notation "χ" => WilsonSeparatedOriginalThermometerCells.positions (R:=R) r z
local notation "wt" => WilsonSeparatedOriginalThermometerCells.weight

/-- The physical, oriented grade-six and two grade-four filings are evaluated
    on their independent cutoff sites. A face reader may use all seven jointly. -/
theorem original {w : ℕ} (h : w ≤ z.1) (φ : Test 3) (read : (Badge → ℂ) → ℂ) :
    let cell := R.family.S.toDepth h z.2
    (φ.applyTo (fun y => read (row A z (χ y))) =
        ∑ c : Fin 3 → Site (R.family.side w z.2), ∑ t : Fin 3 → Site cell.count,
          let y := fun i => cell.assemble (c i,t i)
          wt φ χ y * read (row A z y)) ∧
      (∑ c : Fin 3 → Site (R.family.side w z.2), ∑ t : Fin 3 → Site cell.count,
        ‖wt φ χ (fun i => cell.assemble (c i,t i))‖) ≤ ∫ y : Points 3, ‖φ y‖ := by
  constructor
  · rw [WilsonSeparatedOriginalThermometerCells.tested φ χ
      (WilsonSeparatedOriginalThermometerCells.placed (R:=R) r z)
      (fun y => read (row A z y))]
    exact census (C:=R.family) h _
  · exact (census (C:=R.family) h (fun y => ‖wt φ χ y‖)).symm.le.trans
      (WilsonSeparatedOriginalThermometerCells.variation φ χ
        (WilsonSeparatedOriginalThermometerCells.placed (R:=R) r z))

end YM.Integration.WilsonAddressedCollarFolds
