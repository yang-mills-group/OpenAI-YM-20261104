import YM.Integration.FullQLocalNumericSchedule
import YM.Integration.LocalComparisonReclosure
import YM.IterationFour.Running

/-! A scalar consequence of the complete marked comparison price.
The fixed choice delta=1 uses no new analytic estimate. The geometric
subpower bound at exponent 1/2 and the designated calibration's order-three
tail retain both inherited terms. Block-cover multiplicity is paid separately. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.LocalComparison

/-- The complete markedRate, including inherited error and calibration,
is bounded by a fixed multiple of the square of the coupling. -/
theorem numeric_markedRate_one_le_square {order : ℕ}
    {constant geometry inherited calibration coupling bound eta : ℝ}
    (hOrder : 2 ≤ order) (hEta : eta < 1 / 2)
    (hConstant : 0 ≤ constant) (hGeometry : 0 ≤ geometry)
    (hBound : 0 ≤ bound)
    (hInherited : inherited ≤ bound * coupling ^ ((order : ℝ) + 1 - eta))
    (hCoupling : 0 < coupling) (hSmall : coupling ≤ 1)
    (hGeometric : geometry ≤ coupling ^ (-(1 / 2 : ℝ)))
    (hCalibration : calibration ≤ coupling ^ 3) :
    markedRate order 1 constant geometry inherited calibration coupling ≤
      (constant + bound + 1) * coupling ^ 2 := by
  have hOrderReal : (2 : ℝ) ≤ (order : ℝ) := by exact_mod_cast hOrder
  have hSquare : coupling ^ (2 : ℝ) = coupling ^ 2 :=
    Real.rpow_natCast coupling 2
  have hTaylor : constant * coupling ^ ((order : ℝ) + 1 - 1) ≤
      constant * coupling ^ 2 := by
    rw [← hSquare]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge hCoupling hSmall (by linarith)) hConstant
  have hInheritedTerm : geometry * inherited ≤ bound * coupling ^ 2 := by
    calc
      geometry * inherited ≤
          geometry * (bound * coupling ^ ((order : ℝ) + 1 - eta)) :=
        mul_le_mul_of_nonneg_left hInherited hGeometry
      _ ≤ coupling ^ (-(1 / 2 : ℝ)) *
          (bound * coupling ^ ((order : ℝ) + 1 - eta)) :=
        mul_le_mul_of_nonneg_right hGeometric
          (mul_nonneg hBound (Real.rpow_nonneg hCoupling.le _))
      _ = bound * coupling ^ (-(1 / 2 : ℝ) + ((order : ℝ) + 1 - eta)) := by
        rw [Real.rpow_add hCoupling]
        ring
      _ ≤ bound * coupling ^ (2 : ℝ) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_ge hCoupling hSmall (by linarith)) hBound
      _ = bound * coupling ^ 2 := by rw [hSquare]
  have hCalibrationTerm : geometry * calibration ≤ coupling ^ 2 := by
    calc
      geometry * calibration ≤ geometry * coupling ^ 3 :=
        mul_le_mul_of_nonneg_left hCalibration hGeometry
      _ ≤ coupling ^ (-(1 / 2 : ℝ)) * coupling ^ 3 :=
        mul_le_mul_of_nonneg_right hGeometric (pow_nonneg hCoupling.le _)
      _ = coupling ^ (-(1 / 2 : ℝ) + 3) := by
        rw [Real.rpow_add hCoupling]
        exact congrArg (fun t : ℝ => coupling ^ (-(1 / 2 : ℝ)) * t)
          (Real.rpow_natCast coupling 3).symm
      _ ≤ coupling ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge hCoupling hSmall (by norm_num)
      _ = coupling ^ 2 := hSquare
  unfold markedRate
  calc
    constant * coupling ^ ((order : ℝ) + 1 - 1) +
        geometry * (inherited + calibration) =
        constant * coupling ^ ((order : ℝ) + 1 - 1) +
          geometry * inherited + geometry * calibration := by ring
    _ ≤ constant * coupling ^ 2 + bound * coupling ^ 2 + coupling ^ 2 :=
      add_le_add (add_le_add hTaylor hInheritedTerm) hCalibrationTerm
    _ = (constant + bound + 1) * coupling ^ 2 := by ring

end YM.Integration.LocalComparison

namespace YM.Integration.FullQLocal.RenderedStep
open Filter Lattice Wilson RG LocalComparison
open scoped Topology

variable {G : Gauge} {V : Type} {C : Family G} {J : Request V}
    {A : NumericSchedule C J}

/-- One actual stage event precedes every cutoff and period. The complete
marked price at delta=1 is bounded without altering the selected output. -/
theorem NumericPrices.eventually_markedRate_square (K : NumericPrices A)
    (hG : G.Simple) (hC : C.Makes) :
    ∀ᶠ m : ℕ in atTop, ∀ N period : ℕ, m < N →
      ∀ inherited calibration : ℝ,
        inherited ≤ J.inheritedConstant *
          Pert.Asymptotics.regulatorRun C N period (m + 1) ^
            ((J.order : ℝ) + 1 - J.eta) →
        calibration ≤ Pert.Asymptotics.regulatorRun C N period (m + 1) ^ 3 →
        markedRate J.order 1 (K.markedConstant 1) (K.geometry m)
          inherited calibration (Pert.Asymptotics.regulatorRun C N period (m + 1)) ≤
          (K.markedConstant 1 + J.inheritedConstant + 1) *
            Pert.Asymptotics.regulatorRun C N period (m + 1) ^ 2 := by
  obtain ⟨firstGeometry, hGeometry⟩ := K.subpower (1 / 2) (by norm_num)
  obtain ⟨firstCoupling, hSmall⟩ := eventually_atTop.mp
    (IterationFour.Currency.g_small hG hC 1 zero_lt_one)
  filter_upwards [eventually_ge_atTop firstGeometry,
    eventually_ge_atTop firstCoupling] with m hmGeometry hmCoupling
  intro N period hN inherited calibration hInherited hCalibration
  have hg : 0 < Pert.Asymptotics.regulatorRun C N period (m + 1) :=
    IterationFour.Currency.g_pos hC N period (m + 1) (by omega)
  have hgSmall : Pert.Asymptotics.regulatorRun C N period (m + 1) ≤ 1 :=
    (hSmall (m + 1) (by omega) N period (by omega)).le
  exact numeric_markedRate_one_le_square J.order_ge_two J.eta_lt_half
    (K.marked_constant_nonnegative 1 zero_lt_one) (K.geometry_nonnegative m)
    J.inherited_constant_nonnegative hInherited hg hgSmall
    (hGeometry m hmGeometry N period hN) hCalibration

/-- The designated calibration's order-three tail discharges the preceding
pointwise calibration bound on the original admitted period domain. -/
theorem NumericPrices.eventually_markedRate_square_of_calibration (K : NumericPrices A)
    (hG : G.Simple) (hC : C.Makes)
    (eta_w : ℕ → ℕ → ℕ → ℝ)
    (hCalibration : ∀ᶠ m : ℕ in atTop, ∀ N period : ℕ, m < N →
      J.physicalPeriodLower ≤ (C.S.period period).val →
      eta_w N period m ≤ Pert.Asymptotics.regulatorRun C N period (m + 1) ^ 3) :
    ∀ᶠ m : ℕ in atTop, ∀ N period : ℕ, m < N →
      J.physicalPeriodLower ≤ (C.S.period period).val →
      ∀ inherited : ℝ,
        inherited ≤ J.inheritedConstant *
          Pert.Asymptotics.regulatorRun C N period (m + 1) ^
            ((J.order : ℝ) + 1 - J.eta) →
        markedRate J.order 1 (K.markedConstant 1) (K.geometry m)
          inherited (eta_w N period m)
          (Pert.Asymptotics.regulatorRun C N period (m + 1)) ≤
          (K.markedConstant 1 + J.inheritedConstant + 1) *
            Pert.Asymptotics.regulatorRun C N period (m + 1) ^ 2 := by
  filter_upwards [K.eventually_markedRate_square hG hC, hCalibration]
    with m hRate hCal
  intro N period hN hPeriod inherited hInherited
  exact hRate N period hN inherited (eta_w N period m) hInherited
    (hCal N period hN hPeriod)

end YM.Integration.FullQLocal.RenderedStep
end
