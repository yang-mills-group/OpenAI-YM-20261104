import YM.Integration.WilsonMSbarStandaloneCorrelation

/-! Heat allocation for the converted public correlation coefficient. -/

noncomputable section

namespace YangMills.Matching.CorrelationOnly

open scoped BigOperators Classical

variable {g : GaugeGroup} {B : Maxwell.Reference g}

theorem couplingPowerAbove (f : ℕ → ℝ) (zero : f 0 = 0) {j k : ℕ}
    (above : k < j) : couplingPower f j k = 0 := by
  induction j generalizing k with
  | zero => omega
  | succ j ih =>
      rw [couplingPower]
      apply Finset.sum_eq_zero
      intro i _
      by_cases atZero : i.val = 0
      · rw [atZero, zero, zero_mul]
      · have hi := i.isLt
        have lower : k - i.val < j := by omega
        rw [ih lower, mul_zero]

theorem converted_eq (S : Conversion B) (M N : MSbar.Coefficients B)
    (same : M.correlation = N.correlation) {n : ℕ}
    (k : ℕ) (a : Fin n → Label B) (x : Points n) :
    S.correlation M k a x = S.correlation N k a x := by
  simp only [Conversion.correlation, same]

theorem allocated (S : Conversion B) (M : MSbar.Coefficients B) {n : ℕ}
    (k : ℕ) (a : Fin n → Label B) (x : Points n) :
    S.correlation M k a x =
      ∑ ν : Fin n → Fin (k + 1), ∑ j : Fin (k + 1),
        let used := ∑ i, (ν i).val
        if used + j.val ≤ k then
          (couplingPower S.f j.val (k - used) : ℂ) *
            M.correlation n j.val (S.inputs a ν) x
        else 0 := by
  unfold Conversion.correlation
  apply Finset.sum_congr rfl
  intro ν _
  apply Finset.sum_congr rfl
  intro j _
  let used := ∑ i, (ν i).val
  change (if used ≤ k then
      (couplingPower S.f j.val (k - used) : ℂ) *
        M.correlation n j.val (S.inputs a ν) x else 0) =
    (if used + j.val ≤ k then
      (couplingPower S.f j.val (k - used) : ℂ) *
        M.correlation n j.val (S.inputs a ν) x else 0)
  by_cases fits : used + j.val ≤ k
  · have available : used ≤ k := by omega
    rw [if_pos available, if_pos fits]
  · rw [if_neg fits]
    by_cases available : used ≤ k
    · have lower : k - used < j.val := by omega
      have vanishes := couplingPowerAbove S.f S.f_zero lower
      rw [if_pos available, vanishes]
      simp
    · rw [if_neg available]

end YangMills.Matching.CorrelationOnly

end
