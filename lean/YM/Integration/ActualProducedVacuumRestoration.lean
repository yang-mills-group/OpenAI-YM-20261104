import YM.Integration.LocalComparisonGlobalContract
import YM.Comparison.RG02.Integral.Model
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Pane.Null

/-!
Exact vacuum restoration for the same selected Plan.

The layer coupling h remains separate from the original coupling g.  All
negative-power cancellations are on the nonzero-coupling domain.  The native
model action is identified only where its original flags are absent.  This
file supplies no joint analyticity or relative rank/power fact: the canonical
layer construction must still prove rank <= power + 2, or prove a genuine
cancellation, before an analytic next-Colors vacuum can be asserted.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualProducedVacuumRestoration
open Lattice Wilson RG
open IterationFour IterationFour.Vacuum
open LocalComparison.Global Comparison.RG02

variable {G : Gauge} {n : Side}

/-- Restoring the original inverse-square action shifts the integer degree. -/
theorem prefactor_zpow (a : Piece G n) {h : ℝ} (hh : h ≠ 0) :
    h ^ 2 * Render.prefactor h a =
      h ^ ((2 : ℤ) + Render.stepOrder a) := by
  rw [Render.prefactor, zpow_add₀ hh, zpow_ofNat]

/-- A nonnegative restored degree needs the literal relative rank bound. -/
theorem prefactor_nat (a : Piece G n) {h : ℝ} (hh : h ≠ 0)
    (ha : a.rank ≤ a.power + 2) :
    h ^ 2 * Render.prefactor h a = h ^ (a.power + 2 - a.rank) := by
  rw [prefactor_zpow a hh]
  have he : (2 : ℤ) + Render.stepOrder a =
      ((a.power + 2 - a.rank : ℕ) : ℤ) := by
    unfold Render.stepOrder
    omega
  rw [he, zpow_natCast]

/-- Changing the layer coupling retains the complete original-square ratio. -/
theorem prefactor_changed (a : Piece G n) (g : ℝ) {h : ℝ} (hh : h ≠ 0)
    (ha : a.rank ≤ a.power + 2) :
    g ^ 2 * Render.prefactor h a =
      (g / h) ^ 2 * h ^ (a.power + 2 - a.rank) := by
  calc
    _ = (g / h) ^ 2 * (h ^ 2 * Render.prefactor h a) := by
      field_simp
    _ = _ := by rw [prefactor_nat a hh ha]

/-- The native inverse-square-root coupling has this exact square ratio. -/
theorem gain_ratio (g : ℝ) {beta : ℝ} (hb : 0 ≤ beta) :
    (g / Currency.gain beta) ^ 2 = g ^ 2 * beta := by
  rw [Currency.gain, div_inv_eq_mul, mul_pow, Real.sq_sqrt hb]

variable {C : Family G} {N period order : ℕ}

/-- No beta increment is dropped when converting the actual Plan coupling. -/
theorem model_ratio (P : Plan C N period order) (m : ℕ) {g : ℝ}
    (hg : g ≠ 0) (hb : 0 ≤ (g ^ 2)⁻¹ + P.poly m g) :
    (g / Currency.gain ((g ^ 2)⁻¹ + P.poly m g)) ^ 2 =
      1 + g ^ 2 * P.poly m g := by
  rw [gain_ratio g hb, mul_add, mul_inv_cancel₀ (pow_ne_zero 2 hg)]

/-- The full unmasked extra vacuum, before division by the original g^2.
The retained path, its complete beta increment, and the actual nonlinear
layer coupling are all unchanged.  The loop remains in its native position
outside the inverse-square action. -/
def vacuum (P : Plan C N period order) (m : ℕ) (g : ℝ)
    (U : Config G (C.side m period)) : ℝ :=
  g ^ 2 * (P.poly m g *
    Precision.mainTerm (C.path.levels.params m).clip
      (C.path.rep N period m).path U +
    unmaskedLayers (P.layers m)
      (Currency.gain ((g ^ 2)⁻¹ + P.poly m g)) U)

private theorem square_restore {g : ℝ} (hg : g ≠ 0) (a b c d : ℝ) :
    (g ^ 2)⁻¹ * (a + g ^ 2 * (b * a + c)) + d =
      ((g ^ 2)⁻¹ + b) * a + d + c := by
  field_simp
  ring

/-- Literal equality to the full selected model action on its native
no-flags region.  This is not an assertion at zero coupling or a new law. -/
theorem model_action (P : Plan C N period order) (m : ℕ) {g : ℝ}
    (hg : g ≠ 0) (U : Config G (C.side m period))
    (hU : flags (C.path.levels.budget m).threshold U = ∅) :
    Integral.temperature g *
        (Precision.mainTerm (C.path.levels.params m).clip
          (C.path.rep N period m).path U + vacuum P m g U) +
      Precision.loop (C.path.rep N period m).path U =
        modelAction P m g U := by
  rw [modelAction, PhysicalNext.Repeat.Pane.crystalline _ _ _ _ U hU]
  exact square_restore hg _ _ _ _

end YM.Integration.ActualProducedVacuumRestoration
end
