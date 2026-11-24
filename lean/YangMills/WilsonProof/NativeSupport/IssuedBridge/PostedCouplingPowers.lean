import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedFinitePinCorrelation

namespace IssuedBridge.PostedCouplingPowers
open YM YM.MS YM.FVA2 YangMills.Matching Finset
open scoped BigOperators Classical
noncomputable section

theorem original (c : Book.Program.Cn) (f : ℕ → ℝ)
    (coefficients : ∀ k, PowerSeries.coeff k c = (f k : ℂ)) (j k : ℕ) :
    Book.Program.cut c j k = (couplingPower f j k : ℂ) := by
  induction j generalizing k with
  | zero => cases k <;> simp [Book.Program.cut, couplingPower]
  | succ j ih =>
    rw [Book.Program.cut, pow_succ', PowerSeries.coeff_mul,
      Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => PowerSeries.coeff a c * PowerSeries.coeff b (c ^ j)) k]
    rw [couplingPower, Complex.ofReal_sum, ← Fin.sum_univ_eq_sum_range (fun a => PowerSeries.coeff a c * PowerSeries.coeff (k-a) (c^j)) (k+1)]
    apply Finset.sum_congr rfl
    intro a ha
    rw [coefficients, Complex.ofReal_mul]
    exact congrArg (fun z : ℂ => (f a.val : ℂ) * z) (ih (k-a.val))

end
end IssuedBridge.PostedCouplingPowers
