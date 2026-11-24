import YM.Integration.LocalComparisonGlobalContract
import YM.Integration.ActualRunStartupInput
import YM.Push.ABSOLUTE_SUMS.Basic

/-! The original Run representation is well formed at a requested weaker
norm. Original rows, masks, forced predicates and moves are unchanged.
Every derivative, direction and support comparison is explicit; the
regular cost remains the original clock allowance. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualRunRequestedNorm

open Lattice Wilson RG
open PhysicalNext.Repeat.Legato
open scoped Classical BigOperators

variable {G : Gauge}

private theorem regular_restrict {n : Side} {p q : BudgetPoint}
    (hthreshold : q.threshold = p.threshold) (horder : q.order ≤ p.order)
    {S : Support n} {F : Config G n → ℝ} (h : p.Regular S F) :
    q.Regular S F := by
  refine ⟨h.sites, h.borel, h.symmetry, ?_, ?_⟩
  · intro U hU
    have hpU : Healthy p.threshold S U := hthreshold ▸ hU
    exact (h.smooth U hpU).of_le (by exact_mod_cast horder)
  · intro U hU D l hl
    exact h.hasDerivs U (hthreshold ▸ hU) D l (lt_of_lt_of_le hl horder)

private theorem bound_restrict {n : Side} {p q : BudgetPoint}
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

private theorem mass_restrict {n : Side} {p q : BudgetPoint}
    (hblock : q.B = p.B) (hexponent : q.supportExponent ≤ p.supportExponent)
    (S : Support n) {c : ℝ} (hc : 0 ≤ c) : q.mass S c ≤ p.mass S c := by
  unfold BudgetPoint.mass
  rw [hblock]
  exact mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hexponent (by positivity))) hc

private theorem EBound_restrict {n : Side} {p q : BudgetPoint}
    (hthreshold : q.threshold = p.threshold) (hblock : q.B = p.B)
    (horder : q.order ≤ p.order) (hpower : q.power ≤ p.power)
    (hexponent : q.supportExponent ≤ p.supportExponent)
    {X : Activities G n} {c : ℝ} (h : X.EBound p c) : X.EBound q c := by
  obtain ⟨v, hv, hs⟩ := h
  refine ⟨v, fun i => bound_restrict hthreshold horder hpower (hv i), ?_⟩
  intro o
  apply Push.AbsoluteSums.budget_mono (hs o)
  · intro i
    split_ifs
    · exact mul_nonneg (Real.exp_nonneg _) (hv i).1
    · exact le_rfl
  · intro i
    split_ifs
    · exact mass_restrict hblock hexponent _ (hv i).1
    · exact le_rfl

/-- The same full representation at any actual level, with the original
regular allowance. No derivative bound is inferred from KBound or from
a mere equality of normalization parameters. -/
def wellFormed (R : Run G) (N p m : ℕ) (hm : m ≤ N) (Q : BudgetPoint)
    (hthreshold : Q.threshold = (R.family.path.rep N p m).p.threshold)
    (hblock : Q.B = (R.family.path.rep N p m).p.B)
    (horder : Q.order ≤ (R.family.path.rep N p m).p.order)
    (hpower : Q.power ≤ (R.family.path.rep N p m).p.power)
    (hexponent : Q.supportExponent ≤ (R.family.path.rep N p m).p.supportExponent) :
    LocalComparison.Global.WellFormed Q (R.family.path.rep N p m) := by
  let h : R.family.path.Conv N p m := R.makes.wilson.represents N p m hm
  refine {
    threshold := hthreshold
    regular := fun i => regular_restrict hthreshold horder (h.good.labels.regular.smooth i)
    regular_sum := fun U => (Activities.ESeries h.good.labels).summable U
    regularCost := R.family.path.levels.clock.allowance m
    regular_cost_nonnegative := ?_
    regular_bound := EBound_restrict hthreshold hblock horder hpower hexponent
      h.good.labels.boundE
    forced := h.good.labels.forced
    moves := h.good.labels.moves }
  obtain ⟨_, _, hs⟩ := h.good.labels.boundE
  exact (tsum_nonneg (hs (0 : Site (R.family.side m p))).1).trans (hs _).2.2

end YM.Integration.ActualRunRequestedNorm
end
