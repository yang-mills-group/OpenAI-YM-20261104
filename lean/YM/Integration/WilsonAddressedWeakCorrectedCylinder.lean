import YM.Integration.WilsonAddressedWeakChamber

/-! The ordinary displaced Gram entry from its three original corrected
cutoff cylinders. The expectation is on the full Wilson law. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonAddressedWeakCorrectedCylinder
open Function Filter Set MeasureTheory Lattice Wilson RG Source RG12 Extra.Histories
open RG05Readout Native Address Many Records Harvest Push.GridApprox Cells Extraction
open PhysicalNext.Repeat.Legato MergeProof Accent Motion Bandage Extra.Multi Menu
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetResidue
open WilsonAddressedWeakPointCells
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G) {N p k : ℕ}
variable (d : Fin 2 → ℕ) (z : Fin 2 → Site (R.family.side N p))
  (y : (i:Fin 2) → Palette R.family (d i)) (r : (i:Fin 2) → Emblems R.family (d i))
  (live : k ≤ N) (a : Fin 2 → ℂ) (q : ℂ)
local notation "F" => WilsonThermometerIntrinsicRoster.source R d z y r live
local notation "β" => R.family.beta N p

def full : (Stock.census (Fin 2)).Mode := ⟨Finset.univ,Finset.mem_univ _⟩
def single (i : Fin 2) (U : Config G (R.family.side N p)) := F i U-a i
local notation "S" => single R d z y r live a
def couple (U : Config G (R.family.side N p)) := (S 0 U)*(S 1 U)-(q-a 0*a 1)
local notation "H" => couple R d z y r live a q

private theorem continuous (i : Fin 2) : Continuous (F i) := by
  change Continuous (fun U => (R.family.S.a k:ℂ)^(d i) • R.family.O N p _ (z i) U)
  exact (R.family.continuousO N p (d i) _ (z i)).const_smul ((R.family.S.a k:ℂ)^(d i))

theorem signed :
    reading R d z y r live full - q =
      moment β H + a 1*moment β (S 0) + a 0*moment β (S 1) := by
  let ν := law G (R.family.side N p) β
  have f (i:Fin 2) := continuous R d z y r live i
  have cs (i:Fin 2) : Continuous (S i) := (f i).sub continuous_const
  have ch : Continuous H := ((cs 0).mul (cs 1)).sub continuous_const
  have pay {g : Config G (R.family.side N p) → ℂ} (c : Continuous g) : Integrable g ν :=
    Wilson.continuous_integrable β c
  have pp : Integrable (fun U => F 0 U*F 1 U) ν := pay ((f 0).mul (f 1))
  have cc : Integrable (fun _ : Config G (R.family.side N p) => q) ν := integrable_const _
  have p₁ : Integrable (fun U => a 1*S 0 U) ν := pay ((cs 0).const_mul _)
  have p₀ : Integrable (fun U => a 0*S 1 U) ν := pay ((cs 1).const_mul _)
  have hh : Integrable (fun U => H U+a 1*S 0 U) ν := (pay ch).add p₁
  rw [WilsonAddressedWeakRootedReading.measured]
  change (∫ U, ∏ i ∈ Finset.univ,F i U ∂ν) -q = _
  simp only [Fin.prod_univ_two]
  calc _ = ∫ U, F 0 U*F 1 U-q ∂ν := by rw [integral_sub pp cc];simp [ν]
       _ = ∫ U, H U+a 1*S 0 U+a 0*S 1 U ∂ν := by
         apply integral_congr_ae
         filter_upwards with U
         dsimp only [couple,single]
         ring
       _ = _ := by
         rw [integral_add hh p₀,integral_add (pay ch) p₁,integral_const_mul,integral_const_mul]
         rfl

theorem original (T : Tiling (R.family.side N p))
    (enrolled : ∀ i,Interior (T.chamber 0) (F i)) :
    ‖reading R d z y r live full-q‖ ≤
      T.rootTest β H + ‖a 1‖*T.rootTest β (S 0) + ‖a 0‖*T.rootTest β (S 1) := by
  have ins (i:Fin 2) : Interior (T.chamber 0) (S i) := by
    change Interior (T.chamber 0) (fun U => F i U-a i)
    simp only [sub_eq_add_neg];exact (enrolled i).plus (Interior.constant _ _)
  have inc : Interior (T.chamber 0) H := by
    change Interior (T.chamber 0) (fun U => S 0 U*S 1 U-(q-a 0*a 1))
    simp only [sub_eq_add_neg];exact ((ins 0).times (ins 1)).plus (Interior.constant _ _)
  have tested (F' : Config G (R.family.side N p) → ℂ) (hf : Interior (T.chamber 0) F') :
      ‖moment β F'‖ ≤ T.rootTest β F' := by
    simpa only [Fintype.prod_unique,Tiling.copy_zero] using T.planted
      (Cells.laws G _ β (Overlay.beta_positive R.makes.wilson le_rfl).le) (fun _ : Unit=>0)
      (injective_of_subsingleton _) (fun _ : Unit=>F') (fun _=>hf)
  rw [signed]
  have h₁ := norm_add_le (moment β H) (a 1*moment β (S 0))
  have h₂ := norm_add_le (moment β H+a 1*moment β (S 0)) (a 0*moment β (S 1))
  rw [norm_mul] at h₁ h₂
  linarith only [h₁,h₂,tested _ inc,mul_le_mul_of_nonneg_left (tested _ (ins 0)) (norm_nonneg (a 1)),
    mul_le_mul_of_nonneg_left (tested _ (ins 1)) (norm_nonneg (a 0))]

end YM.Integration.WilsonAddressedWeakCorrectedCylinder
