import YM.Integration.WilsonAddressedWeakCopiedProducts

/-! The compensated reflected measurement at every receiving date on the selected original Wilson course. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonAddressedWeakStampedCourse
open Function Set Filter MeasureTheory Lattice Wilson RG Source RG12 Extra.Histories
open RG05Readout Native Address Many Records Harvest Push.GridApprox Cells Extraction
open PhysicalNext.Repeat.Legato MergeProof Accent Motion Bandage Extra.Multi Menu
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetResidue Marker Push.Corrected Marks
open scoped Classical BigOperators

variable {G:Gauge} (R:Run G)
def wire (χ k N p:ℕ) : Wire R.family χ k N p where
  cost := R.family.path.β N p
  chosen _ _ _ := rfl
  pays _ _ hn := Overlay.beta_positive R.makes.wilson hn

theorem measured {χ k j N p:ℕ} {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X:Config G (R.family.side N p)→E) (hj:j≤N) :
    (wire R χ k N p).push X j hj = gust R.family.path N p N X j hj := by
  induction hj using Nat.decreasingInduction with
  | self => rw [Wire.own,gust_base]
  | of_succ m hm ih => rw [Wire.pushes _ _ m hm,gust_step _ _ _ _ _ hm,ih];rfl

variable {χ k N p:ℕ} (gr:χ≤k) (live:k≤N) (d:Fin 2→ℕ) (z:Fin 2→Site (R.family.side N p))
  (y:(i:Fin 2)→Palette R.family (d i)) (r:(i:Fin 2)→Emblems R.family (d i))
local notation "T" => Cells.center R.family.S p (gr.trans live) 0
local notation "J" => Site (R.family.side χ p)
local notation "F" => WilsonThermometerIntrinsicRoster.source R d z y r live
local notation "X" => Accent.birth (Stock.census (J × Fin 2)) (R.family.path.rep N p N)
  (WilsonAddressedWeakCopiedProducts.field R gr live d z y r)
local notation "W" => wire R χ k N p
local notation "O" => (fun U:Config G (R.family.side N p)=>Marks.ordinary (fun i=>F i U))

private theorem continuous (s:(Stock.census (Fin 2)).Mode) : Continuous (fun U=>(O U).part s) := by
  change Continuous (fun U=>Marks.part (O U) s.val)
  simp_rw [Marks.selects]
  apply continuous_finsetProd
  intro i _
  change Continuous (fun U => (R.family.S.a k:ℂ)^(d i) • R.family.O N p _ (z i) U)
  exact (R.family.continuousO N p (d i) _ (z i)).const_smul ((R.family.S.a k:ℂ)^(d i))

theorem original {j:ℕ} (hj:j≤N) (U:Config G (R.family.side j p)) :
    (W).station (gr.trans live) hj O U = gust R.family.path N p N X j hj U := by
  have hX : Continuous X := by
    change Continuous (fun U=>(X U).part)
    apply continuous_pi
    intro s
    simp_rw [WilsonAddressedWeakCopiedProducts.original R gr live d z y r s]
    exact (Complex.continuous_ofReal.comp (bare_cont _)).mul
      (continuous_array T O (fun b=>continuous R live d z y r (mode b)) s.val)
  have hx : Integrable X (prior G _) := hX.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [← measured (χ:=χ) (k:=k) R X hj]
  ext s
  let L : Marks.Algebra (J × Fin 2) →L[ℝ] ℂ := {
    toFun v:=v.part s
    map_add' :=fun _ _=>rfl
    map_smul' :=fun _ _=>rfl
    cont:=Poly.part_cont _ }
  have h := (W).linear_image L X hx j hj U
  change (W).push (fun A=>(bare (R.family.beta N p) A:ℂ)*Marks.part (Marks.replicate T O A) s.val) j hj U=_
  convert! h using 1
  exact congrFun (congrArg (fun f=>(W).push f j hj)
    (funext fun A=>(WilsonAddressedWeakCopiedProducts.original R gr live d z y r s A).symm)) U

/-- The original enrolled joint source is unchanged until all reflected tests have been filed; its fixed independent subtraction acts on this same pushed density. -/
theorem compensated (a : Fin 2→ℂ) (q:ℂ) {j:ℕ} (hj:j≤N) (U:Config G (R.family.side j p)) :
    let L := Poly.pass (-WilsonAddressedWeakPackedCertificate.cumulant a q)
    (W).station (gr.trans live) hj (WilsonAddressedWeakPackedCertificate.inserted R d z y r live a q) U =
      (∏ i:J,Marks.into (Marks.atHand T i L) i)*gust R.family.path N p N X j hj U := by
  dsimp only
  rw [←original R gr live d z y r hj U]
  exact (W).station_one _ O (continuous R live d z y r) (gr.trans live) hj U

end YM.Integration.WilsonAddressedWeakStampedCourse
