import YM.SectorNext.VACUUM_NORMALIZATION.Stripped
import YM.FullVolume.Cross

/-! Integration of a pointwise relative bound on the literal retained history.
The pointwise bound is the remaining analytic input. The positive reference
and its normalization are supplied by the original Run, not a replacement gas.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualCoveredNormalization
open MeasureTheory Lattice RG Wilson PhysicalNext.Repeat.Legato
open scoped Classical BigOperators
variable {G : Gauge}

/-- The literal coarse density supplies the original fine Wilson mass. -/
theorem same_run_reference (R : Run G) (N p m : ℕ) (hm : m ≤ N) :
    (∀ U, 0 < (R.family.path.rep N p m).eval U) ∧
    Integrable (R.family.path.rep N p m).eval (prior G (R.family.path.S.side m p)) ∧
    (∫ U, (R.family.path.rep N p m).eval U ∂prior G (R.family.path.S.side m p)) =
      partition G (R.family.path.S.side N p) (R.family.path.β N p N) := by
  exact ⟨SectorNext.Vacuum.strictly R.family.path R.makes.wilson N p m hm,
    ((R.family.path.rep N p m).envelope (R.makes.wilson.represents N p m hm).good).integrable _,
    R.family.path.partition_eq R.makes.wilson N p m hm⟩

/-- No volume-dependent lower bound on Z is used. Any genuine pointwise
relative estimate integrates against the original probability Haar measure. -/
theorem normalized (R : Run G) (N p m : ℕ) (hm : m ≤ N)
    (F : Config G (R.family.path.S.side m p) → ℂ) (C : ℝ)
    (hF : Integrable F (prior G (R.family.path.S.side m p)))
    (hbound : ∀ U, ‖F U‖ ≤ C * (R.family.path.rep N p m).eval U) :
    ‖((partition G (R.family.path.S.side N p) (R.family.path.β N p N) : ℝ) : ℂ)⁻¹ *
      (∫ U, F U ∂prior G (R.family.path.S.side m p))‖ ≤ C := by
  obtain ⟨_, he, hmass⟩ := same_run_reference R N p m hm
  have hz : 0 < partition G (R.family.path.S.side N p) (R.family.path.β N p N) :=
    partition_pos _
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hz]
  calc
    _ ≤ (partition G (R.family.path.S.side N p) (R.family.path.β N p N))⁻¹ *
        (∫ U, C * (R.family.path.rep N p m).eval U ∂prior G (R.family.path.S.side m p)) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hz.le)
      exact (norm_integral_le_integral_norm F).trans (integral_mono hF.norm (he.const_mul C) hbound)
    _ = C := by rw [integral_const_mul, hmass]; field_simp

end YM.Integration.ActualCoveredNormalization
