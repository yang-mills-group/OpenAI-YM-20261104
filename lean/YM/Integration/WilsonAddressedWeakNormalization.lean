import YM.Integration.WilsonAddressedWeakRootedReading

/-! The full numerical weak calibration on the original two-site course. A
positive real weight for each occupied source is restored after the joint
physical push, so reflected and complex-conjugated copies have the same fee. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonAddressedWeakNormalization
open Function Filter Set MeasureTheory Lattice Wilson RG Source RG12 Extra.Histories
open RG05Readout Native Address Many Records Harvest Push.GridApprox Copper Push Marker
open PhysicalNext.Repeat.Legato MergeProof Accent Motion Bandage Extra.Multi Menu
open Next.Rank Edition Baler Value Glyph Thirst Alarm
open Trace.Physical
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetResidue
open WilsonAddressedWeakPointCells
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G) {k N p e : ℕ}
variable (d : Fin 2 → ℕ) (z : Fin 2 → Site (R.family.side N p))
  (y : (i:Fin 2) → Palette R.family (d i)) (r : (i:Fin 2) → Emblems R.family (d i))

def weight (y : Palette R.family e) : ℝ := max 1 (size y)
def unit (y : Palette R.family e) : Palette R.family e := ((weight R y:ℂ)⁻¹) • y

theorem positive (y : Palette R.family e) : 0 < weight R y := (zero_lt_one.trans_le (le_max_left ..))

theorem allowed (y : Palette R.family e) : size (unit R y) ≤ 1 := by
  rw [unit,size_smul,norm_inv,Complex.norm_real,Real.norm_of_nonneg (positive R y).le]
  calc _ ≤ (weight R y)⁻¹ * weight R y := mul_le_mul_of_nonneg_left (le_max_right ..) (inv_nonneg.mpr (positive R y).le)
       _ = 1 := inv_mul_cancel₀ (positive R y).ne'

theorem restored (y : Palette R.family e) : (weight R y:ℂ) • unit R y = y := by
  rw [unit,smul_smul,mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (positive R y).ne'),one_smul]

theorem source (live : k ≤ N) (s : Fin 2 → ℂ) (i : Fin 2) :
    WilsonThermometerIntrinsicRoster.source R d z (fun j => s j • y j) r live i =
      s i • WilsonThermometerIntrinsicRoster.source R d z y r live i := by
  unfold WilsonThermometerIntrinsicRoster.source WilsonThermometerOwnOffsetNectar.birth
  rw [map_smul,Pi.smul_apply]
  let F := (R.family.factory (d i) N p).terminal
  let v : (R.family.labels.level (d i)).Coeff := (finer (r i) live) (y i) (WilsonThermometerOwnOffsetField.primaryLetter (d i))
  change _ • R.family.O N p (F (s i • v)) (z i) = _
  rw [F.map_smul, (R.family.linearO N p (d i) (z i)).map_smul,smul_comm]

theorem charged (live : k ≤ N) (face : (Stock.census (Fin 2)).Mode) :
    reading R d z y r live face = (∏ i ∈ face.val,(weight R (y i):ℂ)) *
      reading R d z (fun i=>unit R (y i)) r live face := by
  let v (i : Fin 2) := unit R (y i)
  let f (i : Fin 2) := WilsonThermometerIntrinsicRoster.source R d z v r live i
  have factor (i : Fin 2) : WilsonThermometerIntrinsicRoster.source R d z y r live i =
      (weight R (y i):ℂ) • f i := by
    simpa only [v,restored] using source R d z v r live (fun j=>(weight R (y j):ℂ)) i
  rw [WilsonAddressedWeakRootedReading.measured,WilsonAddressedWeakRootedReading.measured]
  change (∫ U, ∏ i ∈ face.val, WilsonThermometerIntrinsicRoster.source R d z y r live i U
    ∂law G _ (R.family.beta N p)) = _ * ∫ U, ∏ i ∈ face.val,f i U ∂law G _ (R.family.beta N p)
  simp_rw [factor,Pi.smul_apply,smul_eq_mul,Finset.prod_mul_distrib]
  exact integral_const_mul .. 

theorem paid (live : k ≤ N) (face : (Stock.census (Fin 2)).Mode) (a : ℂ) {δ : ℝ}
    (hit : ‖reading R d z (fun i=>unit R (y i)) r live face -
      a / (∏ i ∈ face.val,(weight R (y i):ℂ))‖ ≤ δ) :
    ‖reading R d z y r live face - a‖ ≤ (∏ i ∈ face.val, weight R (y i)) * δ := by
  let w := ∏ i ∈ face.val, weight R (y i)
  have wp : 0 < w := Finset.prod_pos (fun i _=>positive R (y i))
  have wc : (w:ℂ) = ∏ i ∈ face.val,(weight R (y i):ℂ) := by simp only [w,Complex.ofReal_prod]
  rw [←wc] at hit
  rw [charged,←wc]
  rw [show (w:ℂ)*reading R d z (fun i=>unit R (y i)) r live face-a=
    (w:ℂ)*(reading R d z (fun i=>unit R (y i)) r live face-a/w) by
      field_simp [Complex.ofReal_ne_zero.mpr wp.ne'],norm_mul,Complex.norm_real,Real.norm_of_nonneg wp.le]
  exact mul_le_mul_of_nonneg_left hit wp.le

end YM.Integration.WilsonAddressedWeakNormalization
