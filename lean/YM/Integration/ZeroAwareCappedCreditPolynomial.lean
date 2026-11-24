import YM.Integration.ZeroAwareCappedRenderInvoice

/-! A fixed-rank polynomial majorant for the exact capped intrinsic credit.
The constants precede every period, list, budget point, width and budget.
The original threshold power, true piece cost and all row occurrences remain.
No native growing-order or actual stage-payment conclusion is asserted. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ZeroAwareCappedCreditPolynomial

open Finset Lattice Wilson RG
open IterationFour.Vacuum LocalComparison.Global
open scoped BigOperators

private theorem startup_nonnegative (G : Gauge) (k q o : ℕ) :
    0 ≤ Next.Scheduling.Wages.startup G k q o := by
  have hs : 0 ≤ Next.Scheduling.Wages.slotCost G q o 0 :=
    zero_le_one.trans (Next.Scheduling.Wages.slot_ge G q o 0)
  unfold Next.Scheduling.Wages.startup
  positivity

/-- The original per-piece cost is multiplied by one geometry budget here;
the separate sum of all original piece costs is not consumed in this lemma. -/
theorem credit_bound (G : Gauge) (rankCap o q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℕ,
      ∀ {n : Side} {S : List (Piece G n)} {p : BudgetPoint}
        {width budget : ℝ}
        (H : ZeroAwareVacuumPackets S p rankCap width budget),
      p.order = o → p.power = q → 0 < width →
      ∀ a : Piece G n, a ∈ S →
        ZeroAwareCappedRenderInvoice.credit H a ≤
          C * p.threshold ^ a.rank * (1 + width⁻¹) ^ D *
            budget * H.pieceCost a := by
  let d : Fin (rankCap + 1) → ℕ := fun k =>
    Next.Scheduling.Wages.grade k.val q o
  let c : Fin (rankCap + 1) → ℝ := fun k =>
    Next.Scheduling.Wages.startup G k.val q o *
      (Real.exp 1 * (d k).factorial) * (4 / 3 : ℝ) ^ d k
  let C : ℝ := 1 + ∑ k, c k
  let D : ℕ := Next.Scheduling.Wages.grade rankCap q o
  have hc (k : Fin (rankCap + 1)) : 0 ≤ c k := by
    have hs := startup_nonnegative G k.val q o
    dsimp [c]
    positivity
  have hsum : 0 ≤ ∑ k, c k := Finset.sum_nonneg (fun k _ => hc k)
  have hC : 0 < C := by
    dsimp [C]
    linarith
  refine ⟨C, hC, D, ?_⟩
  intro n S p width budget H ho hq hw a ha
  let i : Fin (rankCap + 1) :=
    ⟨a.rank, Nat.lt_succ_of_le (H.rank_bounded a ha)⟩
  have hd : d i ≤ D := by
    change ((q + 1) * o) * a.rank ≤ ((q + 1) * o) * rankCap
    exact Nat.mul_le_mul_left ((q + 1) * o) (H.rank_bounded a ha)
  have hci : c i ≤ ∑ k, c k :=
    Finset.single_le_sum (fun k _ => hc k) (Finset.mem_univ i)
  have hciC : c i ≤ C := by
    dsimp [C]
    linarith
  let w : ℝ := width⁻¹
  have hw0 : 0 ≤ w := (inv_pos.mpr hw).le
  have hp : (1 + (4 / 3 : ℝ) * w) ^ d i ≤
      (4 / 3 : ℝ) ^ d i * (1 + w) ^ D := by
    have hbase : 0 ≤ 1 + (4 / 3 : ℝ) * w := by positivity
    have hscale : 1 + (4 / 3 : ℝ) * w ≤ (4 / 3 : ℝ) * (1 + w) := by
      nlinarith
    calc
      _ ≤ ((4 / 3 : ℝ) * (1 + w)) ^ d i :=
        pow_le_pow_left₀ hbase hscale (d i)
      _ = (4 / 3 : ℝ) ^ d i * (1 + w) ^ d i := mul_pow _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ 1 + w) hd)
        (by positivity)
  let A : ℝ := Next.Scheduling.Wages.startup G i.val q o *
    (Real.exp 1 * (d i).factorial)
  have hA : 0 ≤ A := by
    have hs := startup_nonnegative G i.val q o
    dsimp [A]
    positivity
  have hinner : A * (1 + (4 / 3 : ℝ) * w) ^ d i ≤
      C * (1 + w) ^ D := by
    calc
      _ ≤ A * ((4 / 3 : ℝ) ^ d i * (1 + w) ^ D) :=
        mul_le_mul_of_nonneg_left hp hA
      _ = c i * (1 + w) ^ D := by dsimp [c, A]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hciC (by positivity)
  have hb : 0 ≤ budget := (Real.exp_pos _).le.trans H.cover_cost
  have hceil :
      ZeroAwareCappedRenderInvoice.factorCeiling
        (G := G) (p := p) (width := width) (budget := budget) a.rank ≤
      C * p.threshold ^ a.rank * (1 + w) ^ D * budget := by
    calc
      _ = (p.threshold ^ a.rank * budget) *
          (A * (1 + (4 / 3 : ℝ) * w) ^ d i) := by
        unfold ZeroAwareCappedRenderInvoice.factorCeiling
        rw [ho, hq]
        dsimp [A, d, i, w]
        ring
      _ ≤ (p.threshold ^ a.rank * budget) * (C * (1 + w) ^ D) :=
        mul_le_mul_of_nonneg_left hinner
          (mul_nonneg (pow_nonneg p.threshold_pos.le _) hb)
      _ = _ := by ring
  change ZeroAwareCappedRenderInvoice.factor H a.rank * H.pieceCost a ≤ _
  exact (mul_le_mul_of_nonneg_right
    (ZeroAwareCappedRenderInvoice.factor_bound H hw a.rank)
    (H.piece_cost_nonnegative a ha)).trans
      (mul_le_mul_of_nonneg_right hceil (H.piece_cost_nonnegative a ha))

end YM.Integration.ZeroAwareCappedCreditPolynomial
end
