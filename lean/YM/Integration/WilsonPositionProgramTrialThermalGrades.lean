import YM.Integration.WilsonOriginalPublicTrialNormalization
import YM.Integration.WilsonThermometerPositionTunedSlope

/-! Reading each thermal grade of the fitted finite source on its full inversion vacuum. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialThermalGrades
open Finset PowerSeries Lattice Wilson RG Labels Source PhysicalNext.Repeat.Legato XSpace
open RegulatorIR.FVAAlt2 PertExtension PertExtension.Orb Precision
open WilsonThermometerPositionTunedSlope (Columns finite paid price)
open WilsonOriginalPublicTrialFigure (weight)
open scoped Classical BigOperators

variable {G : Gauge} (R : Run G) {I : Type} [Fintype I] [LinearOrder I] (d : I → ℕ)
local notation "F" i:max => R.family.labels.level (d i)

def frozen (v : ∀ i, (F i).Coeff) (i : I) (a : (F i).Index) : PowerSeries ℂ :=
  PowerSeries.C (v i a)

omit [LinearOrder I] in
theorem restored {g : ℝ} (hg : g ≠ 0) (v : ∀ i, (F i).Coeff) (a : Columns R d) :
    weight R d g v a * (g : ℂ) ^ Kick.depthF univ d a = ∏ i, v i (a i) := by
  have nonzero : (g : ℂ) ≠ 0 := by exact_mod_cast hg
  simp only [WilsonOriginalPublicTrialFigure.weight, WilsonOriginalPublicTrialFigure.amount,
    Complex.ofReal_inv, Complex.ofReal_pow, prod_mul_distrib, prod_inv_distrib, prod_pow_eq_pow_sum,
    Kick.depthF]
  rw [mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ nonzero), mul_one]

variable (v : (i : I) → (R.family.labels.level (d i)).Coeff)
  (z : I → Cover) (P : Period) (T : P.Tree)

theorem coefficient (q : ℕ) :
    coeff q (paid R d (frozen R d v) (finite R d P z T)) =
      ∑ a : Columns R d, (∏ i, v i (a i)) *
        coeff (q + Kick.depthF univ d a) (WilsonPositionProgramCopyTop.normalized R P d z a T) := by
  rw [paid, map_sum]
  apply sum_congr rfl
  intro a _
  have head : price R d (frozen R d v) a = PowerSeries.C (∏ i, v i (a i)) :=
    (map_prod PowerSeries.C (fun i => v i (a i)) univ).symm
  rw [head, PowerSeries.coeff_C_mul, finite, coeff_mk]

/-- A contribution of physical grade q in the actual measured trial contains the
bare grade q plus the sum of ranks of this particular word. -/
theorem priced {g : ℝ} (hg : g ≠ 0) (q : ℕ) :
    ∑ a : Columns R d, weight R d g v a * (g : ℂ) ^ (q + Kick.depthF univ d a) *
        coeff (q + Kick.depthF univ d a) (WilsonPositionProgramCopyTop.normalized R P d z a T) =
      (g : ℂ) ^ q * coeff q (paid R d (frozen R d v) (finite R d P z T)) := by
  rw [coefficient, mul_sum]
  apply sum_congr rfl
  intro a _
  rw [pow_add, mul_left_comm (weight R d g v a), restored R d hg, mul_assoc]

/-- The price of an honest truncation of the entire measured group function.
Each retained word contributes at its own physical order under the same real
finite Gaussian and vacuum denominator. -/
theorem original {g : ℝ} (hg : g ≠ 0) (D : ChartRatio G) (law : LocalRatio D) (n : ℕ) :
    ∑ t ∈ range (n+1), (g : ℂ) ^ t * coeff t
        (WilsonOriginalPublicTrialNormalization.series R d g v z P T) =
      ∑ t ∈ range (n+1), ∑ a : Columns R d,
        if Kick.depthF univ d a ≤ t then
          (g : ℂ) ^ (t-Kick.depthF univ d a) * (∏ i, v i (a i)) *
            ((YM.FVAAlt2.Fixed.treeMom D (WilsonPositionProgramCopyTop.planted R P d z a)
              (Kick.depthF univ d a) (t-Kick.depthF univ d a) : ℝ) : ℂ)
        else 0 := by
  apply sum_congr rfl
  intro t _
  rw [WilsonOriginalPublicTrialNormalization.original R d g v z P T D law t, mul_sum]
  apply sum_congr rfl
  intro a _
  split
  · rename_i below
    have pow : (g : ℂ)^t = (g : ℂ)^(t-Kick.depthF univ d a) * (g : ℂ)^Kick.depthF univ d a := by
      rw [← pow_add, Nat.sub_add_cancel below]
    rw [pow, ← restored R d hg v a]
    ring
  · simp

end YM.Integration.WilsonPositionProgramTrialThermalGrades
end
