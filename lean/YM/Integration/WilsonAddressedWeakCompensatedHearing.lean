import YM.Integration.WilsonAddressedWeakStampedCourse

/-! Each measured correction uses the same physical partition and the entire pushed reflected source. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonAddressedWeakCompensatedHearing
open Function Set Filter MeasureTheory Lattice Wilson RG Source RG12 Extra.Histories
open RG05Readout Native Address Many Records Harvest Push.GridApprox Cells Extraction
open PhysicalNext.Repeat.Legato MergeProof Accent Motion Bandage Extra.Multi Menu
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetResidue Marker Push.Corrected Marks
open WilsonAddressedWeakPackedCertificate WilsonAddressedWeakStampedCourse
open WilsonAddressedWeakPointCells WilsonAddressedWeakCorrectedCylinder
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) {χ k N p:ℕ} (gr:χ≤k) (live:k≤N)
  (d:Fin 2→ℕ) (z:Fin 2→Site (R.family.side N p))
  (y:(i:Fin 2)→Palette R.family (d i)) (r:(i:Fin 2)→Emblems R.family (d i))
  (a:Fin 2→ℂ) (q:ℂ)
local notation "T" => Cells.center R.family.S p (gr.trans live) 0
local notation "J" => Site (R.family.side χ p)
local notation "F" => WilsonThermometerIntrinsicRoster.source R d z y r live
local notation "W" => wire R χ k N p
local notation "P" => inserted R d z y r live a q
local notation "E" => Poly.pass (-WilsonAddressedWeakPackedCertificate.cumulant a q)
local notation "X" => Accent.birth (Stock.census (J × Fin 2)) (R.family.path.rep N p N)
  (WilsonAddressedWeakCopiedProducts.field R gr live d z y r)
local notation "β" => R.family.beta N p

def report {j:ℕ} (hj:j≤N) (s:Finset (Fin 2)) : ℂ :=
  (∫ U,Marks.part ((∏ c:J,Marks.into (Marks.atHand T c E) c) * gust R.family.path N p N X j hj U)
    (Marks.packed T s) ∂prior G _)/(partition G (R.family.side N p) β:ℂ)

theorem measured {j:ℕ} (hj:j≤N) (s:Finset (Fin 2)) :
    report R gr live d z y r a q hj s =
    moment β (fun U=>Marks.part (Marks.replicate T P U) (Marks.packed T s)) := by
  have cO : Continuous (fun U=>Marks.ordinary (fun i=>F i U)) := by
    change Continuous (fun U=>(Marks.ordinary (fun i=>F i U)).part)
    apply continuous_pi
    intro b
    change Continuous (fun U=>Marks.part (Marks.ordinary (fun i=>F i U)) b.val)
    simp_rw [Marks.selects]
    apply continuous_finsetProd
    intro i _
    change Continuous (fun U => (R.family.S.a k:ℂ)^(d i) • R.family.O N p _ (z i) U)
    exact (R.family.continuousO N p (d i) _ (z i)).const_smul ((R.family.S.a k:ℂ)^(d i))
  have cP : Continuous P := continuous_const.mul cO
  let A := fun U=>Marks.part (Marks.replicate T P U) (Marks.packed T s)
  have cA : Continuous A := continuous_array T P (fun b=>(Poly.part_cont _).comp cP) _
  have bound : Integrable (fun U:Config G (R.family.side N p)=>(bare β U:ℂ)*A U) (prior G _) :=
    ((Complex.continuous_ofReal.comp (bare_cont (G:=G) (n:=R.family.side N p) β)).mul cA).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  change report R gr live d z y r a q hj s = moment β A
  unfold report
  simp_rw [← WilsonAddressedWeakStampedCourse.compensated R gr live d z y r a q hj]
  rw [moment_formula _ _ (continuous_integrable _ cA),div_eq_mul_inv,mul_comm]
  congr 1
  exact (W).mass _ bound j hj

/-- All three charged readings are evaluated on the same actual older held fields before taking the physical scalar. -/
theorem original {j:ℕ} (hj:j≤N) (legal:∀ i,Interior ((T).chamber 0) (F i)) :
    let fee := fun s=>‖report R gr live d z y r a q hj s‖^(Fintype.card J:ℝ)⁻¹
    ‖reading R d z y r live full-q‖ ≤ fee {0,1}+‖a 1‖*fee {0}+‖a 0‖*fee {1} := by
  dsimp only
  simp_rw [measured R gr live d z y r a q hj]
  exact WilsonAddressedWeakPackedCertificate.original R d z y r live a q T legal

end YM.Integration.WilsonAddressedWeakCompensatedHearing
