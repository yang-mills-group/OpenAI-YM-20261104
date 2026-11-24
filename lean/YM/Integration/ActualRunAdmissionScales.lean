import YM.Integration.LocalComparisonJetNormalization
import YM.Integration.LocalComparisonInterface

/-! Native scalar data for the actual full-qlocal Admission.  The original
clock, adjacent stage widths, cover, monitor and fine coupling are retained.
This file supplies the algebraic fields only; it does not assert the late
flatness estimates or identify the physical vacuum calibration. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualRunAdmissionScales
open Filter Lattice RG
open scoped Topology

variable {G : Gauge}

/-- The literal aggregate in the original Fits.logCost receipt. -/
def profileCost (A : Levels G) (m : ℕ) : ℝ :=
  1 + (A.params m).paths + (A.params m).width⁻¹ +
    (A.params m).columns + (A.params m).clip.relaxation +
    (A.params m).supportExponent

lemma profileCost_one (A : Levels G) (m : ℕ) : 1 ≤ profileCost A m := by
  unfold profileCost
  linarith [(A.params m).paths_pos, inv_pos.mpr (A.params m).width_pos,
    (A.params m).columns_ge, (A.params m).clip.radius_pos,
    (A.params m).price_pos]

/-- No new delay is used: the original log-cost receipt pays this aggregate
at every step.  This is the aggregate underlying the checked row_budget. -/
theorem profileCost_le_block (A : Levels G) (m : ℕ) :
    profileCost A (m+1) ≤ ((A.S.block m).val : ℝ) := by
  let t := profileCost A (m+1)
  let L : ℝ := (A.S.block m).val
  let j : ℝ := A.clock.J (m+1)
  have ht : 0 < t := zero_lt_one.trans_le (profileCost_one A (m+1))
  have hL : 1 < L := by
    dsimp only [L]
    exact_mod_cast (show 1 < (A.S.block m).val from by
      have := A.S.block_large m
      omega)
  have hj : 4 ≤ j := by
    dsimp only [j]
    exact_mod_cast A.clock.adm (m+1)
  have hcost := A.fits.logCost m
  change Real.log t / Real.log L ≤ (j^2)⁻¹ at hcost
  have hinv : (j^2)⁻¹ ≤ (1 : ℝ)⁻¹ :=
    inv_anti₀ zero_lt_one (by nlinarith)
  have hlog : Real.log t ≤ Real.log L := by
    have h := (div_le_iff₀ (Real.log_pos hL)).1 (hcost.trans hinv)
    simpa only [inv_one, one_mul] using h
  exact (Real.log_le_log_iff ht (zero_lt_one.trans hL)).1 hlog

lemma profileCost_components (A : Levels G) (m : ℕ) :
    (A.params m).width⁻¹ ≤ profileCost A m ∧
    (A.params m).paths ≤ profileCost A m ∧
    (A.params m).columns ≤ profileCost A m ∧
    (A.params m).clip.relaxation ≤ profileCost A m := by
  have hp := (A.params m).paths_pos
  have hw := inv_pos.mpr (A.params m).width_pos
  have hc := (A.params m).columns_ge
  have hr := (A.params m).clip.radius_pos
  have hs := (A.params m).price_pos
  unfold profileCost
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- Same two original widths; the output width will be exactly half. -/
def pairWidth (A : Levels G) (m : ℕ) : ℝ :=
  min (A.params (m+1)).width (A.params m).width

lemma pairWidth_pos (A : Levels G) (m : ℕ) : 0 < pairWidth A m :=
  lt_min_iff.mpr ⟨(A.params (m+1)).width_pos, (A.params m).width_pos⟩

/-- This rate is positive, at most one, and at most the half-width. -/
def pathRate (A : Levels G) (m : ℕ) : ℝ :=
  pairWidth A m / (pairWidth A m + 2)

lemma pathRate_pos (A : Levels G) (m : ℕ) : 0 < pathRate A m := by
  have hx := pairWidth_pos A m
  unfold pathRate
  positivity

lemma pathRate_inv (A : Levels G) (m : ℕ) :
    (pathRate A m)⁻¹ = 1 + 2 * (pairWidth A m)⁻¹ := by
  rw [pathRate, inv_div, add_div, div_self (pairWidth_pos A m).ne',
    div_eq_mul_inv]

lemma pathRate_width (A : Levels G) (m : ℕ) :
    pathRate A m ≤ pairWidth A m / 2 := by
  have hx := pairWidth_pos A m
  unfold pathRate
  apply (div_le_iff₀ (show 0 < pairWidth A m + 2 by linarith)).2
  nlinarith [sq_nonneg (pairWidth A m)]

/-- Exact extensive scalar list in Global.Admission; no geometry is dropped. -/
def geometryCost (A : Levels G) (m : ℕ) : ℝ :=
  1 + (A.clock.coverSize m : ℝ) + (A.clock.coverSize (m+1) : ℝ) +
    A.clock.monitor m + A.clock.monitor (m+1) +
    A.clock.loopCap m + A.clock.loopCap (m+1) +
    (A.params m).paths + (A.params (m+1)).paths +
    (A.params m).columns + (A.params (m+1)).columns +
    (A.params m).clip.relaxation + (A.params (m+1)).clip.relaxation

lemma geometryCost_nonneg (A : Levels G) (m : ℕ) : 0 ≤ geometryCost A m := by
  have hp := (A.params m).paths_pos
  have hp' := (A.params (m+1)).paths_pos
  have hc := (A.params m).columns_ge
  have hc' := (A.params (m+1)).columns_ge
  have hr := (A.params m).clip.radius_pos
  have hr' := (A.params (m+1)).clip.radius_pos
  have hm : 0 < A.clock.monitor m := Real.exp_pos _
  have hm' : 0 < A.clock.monitor (m+1) := Real.exp_pos _
  have hl := Real.rpow_nonneg (show 0 ≤ A.clock.monitor m from hm.le)
    (A.clock.theta (A.clock.J m))
  have hl' := Real.rpow_nonneg (show 0 ≤ A.clock.monitor (m+1) from hm'.le)
    (A.clock.theta (A.clock.J (m+1)))
  unfold geometryCost Calendar.loopCap
  linarith [Nat.cast_nonneg (α := ℝ) (A.clock.coverSize m),
    Nat.cast_nonneg (α := ℝ) (A.clock.coverSize (m+1))]

/-- The native lower half of Currency.hat_g pays both actual threshold/g
terms uniformly in the cutoff and period, at the original fine index. -/
def unitCost (A : Levels G) (m : ℕ) : ℝ :=
  2 * (A.clock.threshold m + A.clock.threshold (m+1)) /
    A.clock.hatCoupling (m+1)

lemma unitCost_nonneg (A : Levels G) (m : ℕ) : 0 ≤ unitCost A m := by
  have ht : 0 < A.clock.threshold m := (A.budget m).threshold_pos
  have ht' : 0 < A.clock.threshold (m+1) := (A.budget (m+1)).threshold_pos
  have hg := WardBin.stepG A (m+1)
  unfold unitCost
  positivity

/-- One fixed formula covers all displayed costs at every stage. -/
def admittedCost (A : Levels G) (m : ℕ) : ℝ :=
  1 + 3 * (pairWidth A m)⁻¹ + geometryCost A m + unitCost A m

lemma admittedCost_one (A : Levels G) (m : ℕ) : 1 ≤ admittedCost A m := by
  have hx := inv_pos.mpr (pairWidth_pos A m)
  have hgeo := geometryCost_nonneg A m
  have hu := unitCost_nonneg A m
  unfold admittedCost
  linarith

lemma cost_covers_geometry (A : Levels G) (m : ℕ) :
    geometryCost A m ≤ admittedCost A m := by
  have hx := inv_pos.mpr (pairWidth_pos A m)
  have hu := unitCost_nonneg A m
  unfold admittedCost
  linarith

lemma cost_covers_widths (A : Levels G) (m : ℕ) :
    (pairWidth A m)⁻¹ + (pairWidth A m / 2)⁻¹ + 1 ≤ admittedCost A m := by
  have hx := pairWidth_pos A m
  rw [inv_div, div_eq_mul_inv]
  have hgeo := geometryCost_nonneg A m
  have hu := unitCost_nonneg A m
  unfold admittedCost
  linarith

lemma path_rate_cost (A : Levels G) (m : ℕ) :
    (pathRate A m)⁻¹ ≤ admittedCost A m := by
  have hx := inv_pos.mpr (pairWidth_pos A m)
  have hgeo := geometryCost_nonneg A m
  have hu := unitCost_nonneg A m
  rw [pathRate_inv]
  unfold admittedCost
  linarith

lemma cost_covers_units (C : Family G) (hC : C.Makes)
    (m N period : ℕ) (hm : m < N) :
    C.path.levels.clock.threshold m /
        Pert.Asymptotics.regulatorRun C N period (m+1) +
      C.path.levels.clock.threshold (m+1) /
        Pert.Asymptotics.regulatorRun C N period (m+1) ≤
      admittedCost C.path.levels m := by
  let A := C.path.levels
  let g := Pert.Asymptotics.regulatorRun C N period (m+1)
  have hg : 0 < g := IterationFour.Currency.g_pos hC N period (m+1) (by omega)
  have hh := (IterationFour.Currency.hat_g hC N period (m+1) (by omega)).1
  have hhat := WardBin.stepG A (m+1)
  have ht : 0 < A.clock.threshold m := (A.budget m).threshold_pos
  have ht' : 0 < A.clock.threshold (m+1) := (A.budget (m+1)).threshold_pos
  have hbound : A.clock.threshold m / g + A.clock.threshold (m+1) / g ≤
      unitCost A m := by
    rw [← add_div]
    calc
      _ ≤ (A.clock.threshold m + A.clock.threshold (m+1)) /
          (A.clock.hatCoupling (m+1) / 2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (show A.clock.hatCoupling (m+1) / 2 ≤ g by
            change A.clock.hatCoupling (m+1) ≤ 2*g at hh
            linarith)
      _ = unitCost A m := by unfold unitCost; rw [div_div_eq_mul_div]; ring
  have hx := inv_pos.mpr (pairWidth_pos A m)
  have hgeo := geometryCost_nonneg A m
  change A.clock.threshold m / g + A.clock.threshold (m+1) / g ≤ admittedCost A m
  unfold admittedCost
  linarith

/-- Requested derivative orders change only the norm convention. -/
def requestedBudget (A : Levels G) (m q d : ℕ) (s : ℝ)
    (hq : 6 ≤ q) (hd : 2 ≤ d) (hs : 0 < s) : BudgetPoint :=
  { A.budget m with
    order := q
    power := d
    supportExponent := s
    order_ge := hq
    power_ge := hd
    exponent_pos := hs }

lemma requested_norm (C : Family G) (m q d : ℕ) (s : ℝ)
    (hq : 6 ≤ q) (hd : 2 ≤ d) (hs : 0 < s) :
    LocalComparison.NormAt C m (requestedBudget C.path.levels m q d s hq hd hs) q d s :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

end YM.Integration.ActualRunAdmissionScales
end
