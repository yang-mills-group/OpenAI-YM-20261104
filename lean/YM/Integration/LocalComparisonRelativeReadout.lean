import YM.Integration.LocalComparisonReadout
import YM.Integration.LocalComparisonEnvelope

/-!
Restore the announced analytic kernel envelopes in the actual masked log.
The coefficient scaling is a continuous linear equivalence, so it commutes
with the declared sums without changing their convergence convention.  No
physical polynomial or vacuum is replaced by its price normalization.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.LocalComparison
open Lattice Wilson RG Marker Finset Overlay RG3.Forms RG3.Script.Picnic
open scoped BigOperators Classical

variable {V : Type} [DecidableEq V] {R : Census V}

/-- Restoring nonzero mode envelopes is a linear change of coordinates in
the finite coefficient space, not a change of physical field variables. -/
def restoreEnvelope (cost : R.Mode → ℝ) (hcost : ∀ s, 0 < cost s) :
    Poly R ≃L[ℂ] Poly R where
  toFun A := Poly.inject (fun s => (cost s : ℂ) * A.part s)
  invFun A := Poly.inject (fun s => (cost s : ℂ)⁻¹ * A.part s)
  left_inv A := by
    ext s
    change (cost s : ℂ)⁻¹ * ((cost s : ℂ) * A.part s) = A.part s
    rw [← mul_assoc, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (hcost s).ne'), one_mul]
  right_inv A := by
    ext s
    change (cost s : ℂ) * ((cost s : ℂ)⁻¹ * A.part s) = A.part s
    rw [← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (hcost s).ne'), one_mul]
  map_add' A B := by ext s; exact mul_add _ _ _
  map_smul' z A := by ext s; exact mul_left_comm _ _ _
  continuous_toFun := by
    change Continuous (fun A : R.Mode → ℂ => fun s => (cost s : ℂ) * A s)
    fun_prop
  continuous_invFun := by
    change Continuous (fun A : R.Mode → ℂ => fun s => (cost s : ℂ)⁻¹ * A s)
    fun_prop

lemma restoreEnvelope_send (cost : R.Mode → ℝ) (hcost : ∀ s, 0 < cost s)
    (s : R.Mode) (z : ℂ) :
    restoreEnvelope cost hcost (Poly.send s ((cost s)⁻¹ • z)) = Poly.send s z := by
  ext t
  change (cost t : ℂ) * (Poly.send s ((cost s)⁻¹ • z)).part t = (Poly.send s z).part t
  rw [Poly.part_send, Poly.part_send]
  by_cases ht : t = s
  · subst t
    simp only [ite_true, Complex.real_smul, Complex.ofReal_inv]
    rw [← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (hcost s).ne'), one_mul]
  simp only [if_neg ht, mul_zero]

variable {G : Gauge} {n : Side} {X : Type*} {P : Rep G n} {o : V → Site n}
    [Fintype V] (T : Taste X o P R)

/-- Exact restoration of the physical masked log, including global units,
regular terms and every mixed caption. -/
theorem restoreEnvelope_log (cost : R.Mode → ℝ) (hcost : ∀ s, 0 < cost s)
    (x : X) (U : Config G n) :
    restoreEnvelope cost hcost (((priceNormalized cost T).leaf x).log U) =
      (T.leaf x).log U := by
  let E := restoreEnvelope cost hcost
  have hR (i : ℕ) : E (((priceNormalized cost T).leaf x).contents.ray i U) =
      (T.leaf x).contents.ray i U := by
    change E (Poly.send (T.menu.rays i)
      (masked P.p.threshold (T.menu.branch i)
        (fun U => (cost (T.menu.rays i))⁻¹ • T.menu.regular x i U) U)) =
      Poly.send (T.menu.rays i)
        (masked P.p.threshold (T.menu.branch i) (T.menu.regular x i) U)
    by_cases hU : Healthy P.p.threshold (T.menu.branch i) U
    · rw [masked_eq _ _ _ _ hU, masked_eq _ _ _ _ hU]
      exact restoreEnvelope_send cost hcost _ _
    rw [masked_ne _ _ _ _ hU, masked_ne _ _ _ _ hU, Poly.send_zero, map_zero]
  change E (((∑ v, Poly.send (R.fire v)
      ((cost (R.fire v))⁻¹ • T.menu.global x v)) +
      ∑' i, ((priceNormalized cost T).leaf x).contents.ray i U) +
      ∑' i, Poly.send (T.tag i) ((cost (T.tag i))⁻¹ • T.score x i)) = _
  rw [map_add, map_add, map_sum, E.map_tsum, E.map_tsum]
  simp_rw [hR, show ∀ s z, E (Poly.send s ((cost s)⁻¹ • z)) = Poly.send s z
    from restoreEnvelope_send cost hcost]
  rfl

/-- The normalization acts on each actual log coefficient by exactly its
announced mode envelope. -/
theorem priceNormalized_log_part (cost : R.Mode → ℝ) (hcost : ∀ s, 0 < cost s)
    (x : X) (U : Config G n) (s : R.Mode) :
    (((priceNormalized cost T).leaf x).log U).part s =
      (cost s)⁻¹ • ((T.leaf x).log U).part s := by
  have h := congrArg (fun A : Poly R => A.part s) (restoreEnvelope_log T cost hcost x U)
  change (cost s : ℂ) * _ = _ at h
  rw [Complex.real_smul, Complex.ofReal_inv, ← h, ← mul_assoc,
    inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (hcost s).ne'), one_mul]

variable {T} {p : BudgetPoint} {w : V → ℝ} {κ regularPrice forcedPrice : ℝ}
    {cost : R.Mode → ℝ}

/-- The kernel envelope is restored in the actual coefficient bound.
All independent tests and conditioning fields remain quantified uniformly. -/
theorem RelativeBudget.actual_log_coefficient
    (h : RelativeBudget p T w κ cost regularPrice forcedPrice)
    (hthreshold : p.threshold = P.p.threshold) (x : X) (U : Config G n) (s : R.Mode) :
    ‖((T.leaf x).log U).part s‖ ≤
      cost s * ((Fintype.card V * regularPrice) / Poly.toll w s) := by
  have he := congrArg (fun A : Poly R => A.part s)
    (restoreEnvelope_log T cost h.positive x U)
  change (cost s : ℂ) * _ = _ at he
  rw [← he, norm_mul, Complex.norm_real, Real.norm_of_nonneg (h.positive s).le]
  exact mul_le_mul_of_nonneg_left (h.budget.log_coefficient hthreshold x U s)
    (h.positive s).le

/-- The original physical log has the exact relative coefficient price;
neither analytic input costs nor independent mixed coefficients are dropped. -/
theorem RelativeBudget.actual_log_relative_price
    (h : RelativeBudget p T w κ cost regularPrice forcedPrice)
    (hthreshold : p.threshold = P.p.threshold) (x : X) (U : Config G n) :
    (∑ s : R.Mode, (Poly.toll w s / cost s) * ‖((T.leaf x).log U).part s‖) ≤
      Fintype.card V * regularPrice := by
  have he : (∑ s : R.Mode, (Poly.toll w s / cost s) * ‖((T.leaf x).log U).part s‖) =
      Poly.price w (((priceNormalized cost T).leaf x).log U) := by
    unfold Poly.price
    apply sum_congr rfl
    intro s _
    rw [priceNormalized_log_part T cost h.positive x U s, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr (h.positive s).le)]
    ring
  rw [he]
  exact h.budget.log_price hthreshold x U

end YM.Integration.LocalComparison
