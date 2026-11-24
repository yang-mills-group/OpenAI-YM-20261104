import YM.Integration.FullQLocalNumericSchedule
import YM.Integration.LocalComparisonVacuum
import YM.IterationFour.Running

/-! A fixed bound for the complete pre-reset vacuum price.
The actual schedule supplies the coupling, geometric and vanishing events.
A designated calibration family supplies its order-two tail; no cap tending
merely to zero is substituted for that coupling-relative statement. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.LocalComparison

/-- A scalar bound for all three terms of the literal vacuumRate. -/
theorem numeric_vacuumRate_le_fixed {order : ℕ}
    {constant block vanishing geometry inherited calibration coupling bound : ℝ}
    (hConstant : 0 ≤ constant) (hBlock : 1 ≤ block)
    (hVanishing : vanishing ≤ 1) (hGeometry : 0 ≤ geometry)
    (hInherited : 0 ≤ inherited) (hBound : inherited ≤ bound)
    (hCoupling : 0 < coupling) (hSmall : coupling ≤ 1)
    (hGeometric : geometry ≤ coupling⁻¹)
    (hCalibration : calibration ≤ coupling ^ 2) :
    vacuumRate order constant block vanishing geometry inherited calibration coupling ≤
      (constant + 1) * bound + 2 := by
  have hDiv : constant / block ≤ constant := by
    apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hBlock)).2
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hBlock hConstant
  have hInheritedTerm :
      (constant / block + vanishing) * inherited ≤ (constant + 1) * bound :=
    (mul_le_mul_of_nonneg_right (add_le_add hDiv hVanishing) hInherited).trans
      (mul_le_mul_of_nonneg_left hBound (by positivity))
  have hProduct : geometry * coupling ≤ 1 := by
    calc
      geometry * coupling ≤ coupling⁻¹ * coupling :=
        mul_le_mul_of_nonneg_right hGeometric hCoupling.le
      _ = 1 := inv_mul_cancel₀ hCoupling.ne'
  have hTaylor : coupling ^ (order + 1) * geometry ≤ 1 := by
    calc
      coupling ^ (order + 1) * geometry =
          coupling ^ order * (geometry * coupling) := by rw [pow_succ]; ring
      _ ≤ coupling ^ order * 1 :=
        mul_le_mul_of_nonneg_left hProduct (pow_nonneg hCoupling.le _)
      _ ≤ 1 := by simpa only [mul_one] using pow_le_one₀ hCoupling.le hSmall
  have hCalibrationTerm : geometry * calibration ≤ 1 := by
    calc
      geometry * calibration ≤ geometry * coupling ^ 2 :=
        mul_le_mul_of_nonneg_left hCalibration hGeometry
      _ = coupling * (geometry * coupling) := by ring
      _ ≤ coupling * 1 := mul_le_mul_of_nonneg_left hProduct hCoupling.le
      _ ≤ 1 := by simpa only [mul_one] using hSmall
  unfold vacuumRate
  linarith

end YM.Integration.LocalComparison

namespace YM.Integration.FullQLocal.RenderedStep
open Filter Lattice Wilson RG LocalComparison
open scoped Topology

variable {G : Gauge} {V : Type} {C : Family G} {J : Request V}
    {A : NumericSchedule C J}

/-- One actual stage event bounds the full price for every cutoff, period
and inherited error in the stated input class. Only the calibration's
coupling-relative order-two bound is requested at the individual step. -/
theorem NumericPrices.eventually_vacuumRate_bounded (K : NumericPrices A)
    (hG : G.Simple) (hC : C.Makes) :
    ∀ᶠ m : ℕ in atTop, ∀ N period : ℕ, m < N →
      ∀ inherited calibration : ℝ, 0 ≤ inherited →
        inherited ≤ J.inheritedConstant *
          Pert.Asymptotics.regulatorRun C N period (m + 1) ^
            ((J.order : ℝ) + 1 - J.eta) →
        calibration ≤ Pert.Asymptotics.regulatorRun C N period (m + 1) ^ 2 →
        vacuumRate J.order K.vacuumConstant (C.S.block m).val
          (K.vanishing m) (K.geometry m) inherited calibration
          (Pert.Asymptotics.regulatorRun C N period (m + 1)) ≤
          (K.vacuumConstant + 1) * J.inheritedConstant + 2 := by
  obtain ⟨firstGeometry, hGeometry⟩ := K.subpower 1 zero_lt_one
  obtain ⟨firstCoupling, hSmall⟩ := eventually_atTop.mp
    (IterationFour.Currency.g_small hG hC 1 zero_lt_one)
  filter_upwards [K.vanishing_tendsto.eventually (gt_mem_nhds zero_lt_one),
    eventually_ge_atTop firstGeometry, eventually_ge_atTop firstCoupling]
    with m hVanishing hmGeometry hmCoupling
  intro N period hN inherited calibration hInherited hInheritedBound hCalibration
  let g := Pert.Asymptotics.regulatorRun C N period (m + 1)
  have hg : 0 < g := IterationFour.Currency.g_pos hC N period (m + 1) (by omega)
  have hgSmall : g ≤ 1 :=
    (hSmall (m + 1) (by omega) N period (by omega)).le
  have hExponent : 0 ≤ (J.order : ℝ) + 1 - J.eta := by
    have hOrder : (2 : ℝ) ≤ (J.order : ℝ) := by exact_mod_cast J.order_ge_two
    linarith [J.eta_lt_half]
  have hPower : g ^ ((J.order : ℝ) + 1 - J.eta) ≤ 1 :=
    Real.rpow_le_one hg.le hgSmall hExponent
  have hBound : inherited ≤ J.inheritedConstant :=
    hInheritedBound.trans
      (mul_le_of_le_one_right J.inherited_constant_nonnegative hPower)
  have hGeometric : K.geometry m ≤ g⁻¹ := by
    simpa only [Real.rpow_neg_one] using hGeometry m hmGeometry N period hN
  have hBlock : (1 : ℝ) ≤ ((C.S.block m).val : ℝ) :=
    Nat.one_le_cast.mpr (C.S.block m).pos
  exact numeric_vacuumRate_le_fixed K.vacuum_constant_nonnegative hBlock hVanishing.le
    (K.geometry_nonnegative m) hInherited hBound hg hgSmall hGeometric hCalibration

/-- Intersect the preceding actual event with the designated calibration's
order-two tail on the original admitted period domain. -/
theorem NumericPrices.eventually_vacuumRate_bounded_of_calibration (K : NumericPrices A)
    (hG : G.Simple) (hC : C.Makes)
    (eta_w : ℕ → ℕ → ℕ → ℝ)
    (hCalibration : ∀ᶠ m : ℕ in atTop, ∀ N period : ℕ, m < N →
      J.physicalPeriodLower ≤ (C.S.period period).val →
      eta_w N period m ≤ Pert.Asymptotics.regulatorRun C N period (m + 1) ^ 2) :
    ∀ᶠ m : ℕ in atTop, ∀ N period : ℕ, m < N →
      J.physicalPeriodLower ≤ (C.S.period period).val →
      ∀ inherited : ℝ, 0 ≤ inherited →
        inherited ≤ J.inheritedConstant *
          Pert.Asymptotics.regulatorRun C N period (m + 1) ^
            ((J.order : ℝ) + 1 - J.eta) →
        vacuumRate J.order K.vacuumConstant (C.S.block m).val
          (K.vanishing m) (K.geometry m) inherited (eta_w N period m)
          (Pert.Asymptotics.regulatorRun C N period (m + 1)) ≤
          (K.vacuumConstant + 1) * J.inheritedConstant + 2 := by
  filter_upwards [K.eventually_vacuumRate_bounded hG hC, hCalibration]
    with m hRate hCal
  intro N period hN hPeriod inherited hInherited hBound
  exact hRate N period hN inherited (eta_w N period m) hInherited hBound
    (hCal N period hN hPeriod)

end YM.Integration.FullQLocal.RenderedStep
end
