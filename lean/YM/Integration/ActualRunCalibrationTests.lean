import YM.RG05Readout.Test.Levers
import YM.Integration.LocalComparisonInterface

/-! The original finite calibration tests in the native qlocal test space.
The spatial coordinate equivalence and every fixed test price are explicit.
The cell is exactly the native coordinate box, and the functions remain the
original global polynomials. No physical output or comparison estimate is
asserted by this test-admission construction. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualRunCalibrationTests
open Function Finset Lattice Tensor RG05Readout.Native
open ComparisonDensity.Address
open scoped Classical Topology ContDiff

variable {d : ℕ}

/-- The actual underlying coordinates, with both native norm conventions. -/
def coordinates : Pos ≃L[ℝ] E4 :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Axis => ℝ)).symm

def orbit (d D : ℕ) : Orbit := ⟨.cell, D, d⟩

def lineForm (i : Letter d) : Pos → ℂ :=
  (line i).val ∘ coordinates

private theorem line_smooth (D : ℕ) (i : Letter d) :
    ContDiff ℝ D (lineForm i) :=
  (body_smooth (line i) D).comp coordinates.contDiff

theorem coordinate_box (x : Pos) :
    x ∈ (orbit d 0).scope ↔ coordinates x ∈ RG05Readout.Native.box := by
  change x ∈ Metric.closedBall 0 (1 / 2) ↔ ∀ j, |(coordinates x) j| ≤ 1 / 2
  simp only [Metric.mem_closedBall, dist_zero_right]
  change ‖x‖ ≤ 1 / 2 ↔ ∀ j, |x j| ≤ 1 / 2
  exact pi_norm_le_iff_of_nonneg (by norm_num)

/-- A fixed finite price for the actual original polynomial, including the
change from the Euclidean native domain to the qlocal position norm. -/
theorem line_bill (D : ℕ) (i : Letter d) :
    ∃ c > 0, (orbit d D).Bill (lineForm i) c := by
  have hB (k : Fin (D + 1)) :=
    (isCompact_closedBall (0 : Pos) (1 / 2 : ℝ)).exists_bound_of_continuousOn
      ((line_smooth k.val i).continuous_iteratedFDeriv (m := k.val) le_rfl).continuousOn
  choose C h using hB
  have h0 (k : Fin (D + 1)) : 0 ≤ C k :=
    (norm_nonneg _).trans (h k 0 (by simp))
  let c := 1 + ∑ k, C k
  have hc : 0 < c := add_pos_of_pos_of_nonneg zero_lt_one
    (Finset.sum_nonneg fun k _ => h0 k)
  refine ⟨c, hc, hc.le, line_smooth D i, ?_⟩
  intro k hk x hx
  have ht : ‖iteratedFDeriv ℝ k (lineForm i) x‖ ≤ c :=
    (h ⟨k, Nat.lt_succ_of_le hk⟩ x hx).trans
      ((Finset.single_le_sum (fun k _ => h0 k) (Finset.mem_univ _)).trans
        (le_add_of_nonneg_left zero_le_one))
  exact ht.trans (le_mul_of_one_le_left hc.le
    (one_le_pow₀ (le_add_of_nonneg_right (norm_nonneg x))))

def lineCost (D : ℕ) (i : Letter d) : ℝ := (line_bill D i).choose

theorem lineCost_pos (D : ℕ) (i : Letter d) : 0 < lineCost D i :=
  (line_bill D i).choose_spec.1

def unitLine (D : ℕ) (i : Letter d) : Pos → ℂ :=
  ((lineCost D i : ℂ)⁻¹) • lineForm i

theorem unitLine_bill (D : ℕ) (i : Letter d) :
    (orbit d D).Bill (unitLine D i) 1 := by
  have h := ((line_bill D i).choose_spec.2).smul ((lineCost D i : ℂ)⁻¹)
  simpa only [unitLine, lineCost, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (line_bill D i).choose_spec.1,
    inv_mul_cancel₀ (line_bill D i).choose_spec.1.ne'] using h

/-- Every slot has its own admitted unit test; no common test is substituted. -/
def independent (D : ℕ) :
    LocalComparison.IndependentTests (fun _ : Letter d => orbit d D) :=
  fun i => ⟨unitLine D i, unitLine_bill D i⟩

theorem recover_line (D : ℕ) (i : Letter d) :
    (lineCost D i : ℂ) • (independent (d := d) D i).val = lineForm i := by
  change (lineCost D i : ℂ) • (((lineCost D i : ℂ)⁻¹) • lineForm i) = _
  rw [smul_inv_smul₀ (Complex.ofReal_ne_zero.mpr (lineCost_pos D i).ne')]

end YM.Integration.ActualRunCalibrationTests
end
