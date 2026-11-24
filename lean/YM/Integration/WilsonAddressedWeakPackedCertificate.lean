import YM.Integration.WilsonAddressedWeakCorrectedCylinder
import YM.Push.CORRECTED_COLUMNS.Array

/-! The original Wilson block hears all three chessboard coefficients of one compensated two-field insertion. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonAddressedWeakPackedCertificate
open Function Set Filter MeasureTheory Lattice Wilson RG Source RG12 Extra.Histories
open RG05Readout Native Address Many Records Harvest Push.GridApprox Cells Extraction
open PhysicalNext.Repeat.Legato MergeProof Accent Motion Bandage Extra.Multi Menu
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetResidue WilsonAddressedWeakPointCells
open WilsonAddressedWeakCorrectedCylinder Marker Push.Corrected Marks
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G) {N p k : ℕ}
variable (d : Fin 2 → ℕ) (z : Fin 2 → Site (R.family.side N p))
  (y : (i:Fin 2) → Palette R.family (d i)) (r : (i:Fin 2) → Emblems R.family (d i))
  (live : k≤N) (a : Fin 2→ℂ) (q : ℂ)
local notation "F" => WilsonThermometerIntrinsicRoster.source R d z y r live
local notation "β" => R.family.beta N p
local notation "H" => couple R d z y r live a q
local notation "S" => single R d z y r live a

def cumulant (a : Fin 2→ℂ) (q : ℂ) : Algebra (Fin 2) := Poly.inject fun s =>
  if 0∈s.val then (if 1∈s.val then q-a 0*a 1 else a 0) else (if 1∈s.val then a 1 else 0)

private theorem empty : part (cumulant a q) ∅=0 := by simp [Marks.part,Poly.part,Poly.inject,cumulant]
private theorem axis (i:Fin 2) : part (cumulant a q) {i}=a i := by fin_cases i <;> simp [Marks.part,Poly.part,Poly.inject,cumulant]
private theorem connected : part (cumulant a q) {(0:Fin 2),1}=q-a 0*a 1 := by simp [Marks.part,Poly.part,Poly.inject,cumulant]

def inserted (U:Config G (R.family.side N p)) : Algebra (Fin 2) := adjusted (cumulant a q) (fun i=> F i U)
local notation "P" => inserted R d z y r live a q

/-- The exponential compensator acts before multiplication of the copies. -/
theorem coefficients (U:Config G (R.family.side N p)) :
    (∀ i:Fin 2,part (P U) {i}= S i U) ∧ part (P U) {0,1}=H U := by
  constructor
  · intro i; rw [inserted,corrected_single _ (empty ..),axis]; rfl
  · rw [inserted,corrected_pair _ (empty ..) _ _ _ (by decide),axis,axis,connected]; rfl

def expense (T : Tiling (R.family.side N p)) (s : Finset (Fin 2)) :=
  ‖moment β (fun U=>part (replicate T P U) (packed T s))‖^(Fintype.card T.Cell:ℝ)⁻¹

/-- A true pair and both proper faces are read with their original positive Wilson denominator. -/
theorem original (T:Tiling (R.family.side N p)) (legal : ∀ i, Interior (T.chamber 0) (F i)) :
    ‖reading R d z y r live full-q‖ ≤
    expense R d z y r live a q T {0,1} + ‖a 1‖*expense R d z y r live a q T {0}
      + ‖a 0‖*expense R d z y r live a q T {1} := by
  have priced (s:Finset (Fin 2)) (B:Config G (R.family.side N p) → ℂ)
      (hB:∀ U,part (P U) s=B U) : expense R d z y r live a q T s=T.rootTest β B := by
    unfold expense Tiling.rootTest
    simp_rw [folded,hB]
  rw [priced {0,1} H (fun U=>(coefficients R d z y r live a q U).2),
      priced {0} (S 0) (fun U=>(coefficients R d z y r live a q U).1 0),
      priced {1} (S 1) (fun U=>(coefficients R d z y r live a q U).1 1)]
  exact WilsonAddressedWeakCorrectedCylinder.original R d z y r live a q T legal

end YM.Integration.WilsonAddressedWeakPackedCertificate
