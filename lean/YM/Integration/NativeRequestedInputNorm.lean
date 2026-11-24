import YM.Integration.LocalComparisonGlobalContract
import YM.IterationFour.Vacuum.Payload
import YM.Push.ABSOLUTE_SUMS.Basic

/-! Requested-norm conversions on the same physical data. The Payload and
representation remain literal, including every original regular row and
the full forced family. These statements require no Coin and do not impose
affine-null validity on a calibrated representation.

The four private norm-restriction proofs are copied from the corresponding
ActualRunRequestedNorm proofs, with private names changed. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.NativeRequestedInputNorm

open Lattice Wilson RG IterationFour IterationFour.Vacuum
open scoped Classical BigOperators

variable {G : Gauge}

private theorem regular_lower {n : Side} {p q : BudgetPoint}
    (hthreshold : q.threshold = p.threshold) (horder : q.order ≤ p.order)
    {S : Support n} {F : Config G n → ℝ} (h : p.Regular S F) :
    q.Regular S F := by
  refine ⟨h.sites, h.borel, h.symmetry, ?_, ?_⟩
  · intro U hU
    have hpU : Healthy p.threshold S U := hthreshold ▸ hU
    exact (h.smooth U hpU).of_le (by exact_mod_cast horder)
  · intro U hU D l hl
    exact h.hasDerivs U (hthreshold ▸ hU) D l (lt_of_lt_of_le hl horder)

private theorem bound_lower {n : Side} {p q : BudgetPoint}
    (hthreshold : q.threshold = p.threshold) (horder : q.order ≤ p.order)
    (hpower : q.power ≤ p.power) {o : Site n} {S : Support n}
    {F : Config G n → ℝ} {c : ℝ} (h : p.supBounds o S F c) :
    q.supBounds o S F c := by
  refine ⟨h.1, ?_⟩
  intro U hU l hl hD
  apply h.2 U (hthreshold ▸ hU) l (hl.trans horder)
  intro D hDl e
  have hd := hD D hDl e
  rw [hthreshold] at hd
  exact hd.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀
      (le_add_of_nonneg_right (Nat.cast_nonneg (separation e.1 o))) hpower)
    p.threshold_pos.le)

private theorem mass_lower {n : Side} {p q : BudgetPoint}
    (hblock : q.B = p.B) (hexponent : q.supportExponent ≤ p.supportExponent)
    (S : Support n) {c : ℝ} (hc : 0 ≤ c) : q.mass S c ≤ p.mass S c := by
  unfold BudgetPoint.mass
  rw [hblock]
  exact mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hexponent (by positivity))) hc

private theorem EBound_lower {n : Side} {p q : BudgetPoint}
    (hthreshold : q.threshold = p.threshold) (hblock : q.B = p.B)
    (horder : q.order ≤ p.order) (hpower : q.power ≤ p.power)
    (hexponent : q.supportExponent ≤ p.supportExponent)
    {X : Activities G n} {c : ℝ} (h : X.EBound p c) : X.EBound q c := by
  obtain ⟨v, hv, hs⟩ := h
  refine ⟨v, fun i => bound_lower hthreshold horder hpower (hv i), ?_⟩
  intro o
  apply Push.AbsoluteSums.budget_mono (hs o)
  · intro i
    split_ifs
    · exact mul_nonneg (Real.exp_nonneg _) (hv i).1
    · exact le_rfl
  · intro i
    split_ifs
    · exact mass_lower hblock hexponent _ (hv i).1
    · exact le_rfl

/-- Lower only the norm. Every payload row, address, coefficient and cost
remains the original one. -/
theorem invoice_restrict {n : Side} {p q : BudgetPoint}
    {P : Payload G n} {c : ℝ} (h : P.Invoice p c)
    (hthreshold : q.threshold = p.threshold) (hblock : q.B = p.B)
    (horder : q.order ≤ p.order) (hpower : q.power ≤ p.power)
    (hexponent : q.supportExponent ≤ p.supportExponent) :
    P.Invoice q c := by
  refine {
    smooth := fun i => regular_lower hthreshold horder (h.smooth i)
    flat := h.flat
    null := h.null
    moves := h.moves
    credit := ?_ }
  obtain ⟨v, hv, hs⟩ := h.credit
  refine ⟨v, fun i => bound_lower hthreshold horder hpower (hv i), ?_⟩
  intro o
  apply Push.AbsoluteSums.budget_mono (hs o)
  · intro i
    split_ifs
    · exact mul_nonneg (Real.exp_nonneg _) (hv i).1
    · exact le_rfl
  · intro i
    split_ifs
    · exact mass_lower hblock hexponent _ (hv i).1
    · exact le_rfl

/-- The complete masked sum depends only on the unchanged threshold. -/
theorem amount_eq {n : Side} (P : Payload G n) {p q : BudgetPoint}
    (hthreshold : q.threshold = p.threshold) (W : Config G n) :
    P.amount q W = P.amount p W := by
  simp only [Payload.amount, hthreshold]

/-- Restrict the regular norm of the same complete representation.
Its original masked sum, forced family, gas and moves remain unchanged.
No affine-null condition on this calibrated representation is required. -/
def wellFormed_restrict {n : Side} {P : Rep G n} {p q : BudgetPoint}
    (h : LocalComparison.Global.WellFormed p P)
    (hthreshold : q.threshold = p.threshold) (hblock : q.B = p.B)
    (horder : q.order ≤ p.order) (hpower : q.power ≤ p.power)
    (hexponent : q.supportExponent ≤ p.supportExponent) :
    LocalComparison.Global.WellFormed q P where
  threshold := hthreshold.trans h.threshold
  regular i := regular_lower hthreshold horder (h.regular i)
  regular_sum := h.regular_sum
  regularCost := h.regularCost
  regular_cost_nonnegative := h.regular_cost_nonnegative
  regular_bound := EBound_lower hthreshold hblock horder hpower hexponent h.regular_bound
  forced := h.forced
  moves := h.moves

/-- Every original regular row, with its original address and function. -/
def regularPayload {n : Side} (X : Activities G n) : Payload G n :=
  ⟨X.reg, X.E⟩

/-- The actual regular receipt gives a Payload invoice at any weaker norm. -/
theorem regular_invoice {n : Side} {p q : BudgetPoint}
    {X : Activities G n} {c γ : ℝ} (h : X.Valid p c γ)
    (hthreshold : q.threshold = p.threshold) (hblock : q.B = p.B)
    (horder : q.order ≤ p.order) (hpower : q.power ≤ p.power)
    (hexponent : q.supportExponent ≤ p.supportExponent) :
    (regularPayload X).Invoice q c := by
  have hI : (regularPayload X).Invoice p c := {
    smooth := h.regular.smooth
    flat := h.regular.at_flat
    null := h.regular.vanish
    moves := by
      intro s b
      obtain ⟨e⟩ := h.moves s b
      exact ⟨e.ep, fun i => ⟨e.reg_site i, e.reg_support i, e.valuesE i⟩⟩
    credit := h.boundE }
  exact invoice_restrict hI hthreshold hblock horder hpower hexponent

/-- Requested-norm payment does not change the original additive action. -/
theorem regular_amount {n : Side} (X : Activities G n) {p q : BudgetPoint}
    (hthreshold : q.threshold = p.threshold) (W : Config G n) :
    (regularPayload X).amount q W = X.additive p W := by
  rw [amount_eq (regularPayload X) hthreshold W]
  rfl

end YM.Integration.NativeRequestedInputNorm
end
