import YM.Integration.WilsonMacroscopicRichConditionalJet

/-! The original held-field response costs a fixed price before both regulators for a prescribed local family of directions. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichHeldProbePrice
open Function Filter MeasureTheory Lattice Wilson RG Source Push.Local Push.Local.Kernel PhysicalNext.Repeat.Legato RGComparison.Core16
open WilsonMacroscopicRichTransitionIncome
open scoped Classical BigOperators Topology Matrix.Norms.Frobenius
open private invRate_pos from YM.Push.LOCAL_SPLITTING.Response
variable {G : Gauge}

def noise (R : Run G) (u k j : ℕ) (r : ℝ) := (noiseFactor G (2*R.family.path.levels.clock.hatBeta (u+1)*R.family.path.levels.clock.kernel.penalty) k j r)^k

def price (R : Run G) (u k j : ℕ) (r : ℝ) := (2:ℝ)^k * (noise R u k j r * invRate k (noise R u k j r) k)

theorem original (R : Run G) (u k j : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ price R u k j r ∧ ∀ N p : ℕ, ∀(_ : Slices R.family.path.levels p) (_ : u+1 ≤ N)
      (J : Edges (R.family.side u p)), J.card ≤ j → ∀ l : List (Directions G (R.family.side u p)),
      l.length ≤ k → (∀ A∈l,Born J r A) → ∀ V : Config G (R.family.side u p),
    let H := R.family.path
    let S := H.levels.clock.op u p
    let β := H.β N p (u+1)
    let D := fun U : Config G (R.family.side (u+1) p) => leftDerivs (fun W => S.density β U W / (H.rep N p u).eval W) l V
    Measurable D ∧ ∀ U, ‖D U‖ ≤ price R u k j r * (S.density β U V / (H.rep N p u).eval V) := by
  let C := noise R u k j r
  have hC : 1 ≤ C := one_le_pow₀ (noiseFactor_ge G _ k j hr)
  refine ⟨mul_nonneg (by positivity) (mul_nonneg (zero_le_one.trans hC) (zero_le_one.trans (invRate_pos k hC k))),?_⟩
  intro N p T live J hj l hl ha V H S β D
  let X := (H.rep N p (u+1)).eval
  have born : (traversal T live).vacuum (G:=G) (line H p (u+1) N) = X := vacuum_eq T R.makes.wilson live
  have xi : Integrable X (prior G _) := by rw [←born]; exact Descent.output_integrable (traversal_ok T live) _ (bare_integrable _)
  have xp (U) : 0 < X U := born ▸ Descent.positive (line H p (u+1) N) (traversal_ok T live) U
  have fixed : (H.rep N p u).eval = S.push β X := (R.makes.wilson.steps N p u live).1
  have lo : 0 ≤ β := (div_nonneg (zero_lt_one.trans (H.levels.fits.delayed (u+1))).le (by norm_num : 0 ≤ (2:ℝ))).trans (R.makes.wilson.represents N p (u+1) live).band.1
  have hi : β ≤ 2*H.levels.clock.hatBeta (u+1) := (R.makes.wilson.represents N p (u+1) live).band.2
  have speed : |β*S.kernel.penalty| ≤ |2*H.levels.clock.hatBeta (u+1)*H.levels.clock.kernel.penalty| := by
    have same : S.kernel.penalty = H.levels.clock.kernel.penalty := rfl
    rw [abs_mul,abs_mul,same,abs_of_nonneg lo,abs_of_nonneg (lo.trans hi)]
    exact mul_le_mul_of_nonneg_right hi (abs_nonneg _)
  have fee : (noiseFactor G (β*S.kernel.penalty) k J.card r)^k ≤ C := by
    apply pow_le_pow_left₀ (zero_le_one.trans (noiseFactor_ge _ _ _ _ hr))
    unfold noiseFactor scorePrice
    let t := ‖(1:G.Mat)‖ * (1+G.colorScale*r)^k
    have ht : 0 ≤ t := mul_nonneg (norm_nonneg _) (pow_nonneg (by positivity [G.colorScale_pos]) k)
    have inc := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right speed (pairingNorm_nonneg G)) ht
    have val : 0 ≤ |β*S.kernel.penalty| * pairingNorm G * t := mul_nonneg (mul_nonneg (abs_nonneg _) (pairingNorm_nonneg _)) ht
    exact mul_le_mul_of_nonneg_left (add_le_add (le_refl 1) (mul_le_mul (Nat.cast_le.mpr hj) inc val (Nat.cast_nonneg j))) (pow_nonneg (by norm_num) k)
  dsimp only [D]; rw [fixed]
  exact ⟨WilsonMacroscopicRichConditionalJet.measurable S (H.levels.blocks u p).branches β X xi xp V l,
    fun U => WilsonMacroscopicRichConditionalJet.relative S (H.levels.blocks u p).branches β X xi xp J k hr fee U V l hl ha⟩

end YM.Integration.WilsonMacroscopicRichHeldProbePrice
