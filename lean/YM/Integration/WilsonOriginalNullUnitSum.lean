import YM.Integration.WilsonOriginalNullUnitHistory

/-! The actual logarithmic block clock makes all earlier emitted unit fees
summable at fixed upper price, including each truncated prefix of the course. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalNullUnitSum
open Wilson RG Trace.Physical Trace.Physical.GermGraph WilsonOriginalNullCorridor
open scoped BigOperators
variable {G:Gauge} (C:Family G)

def ratio:ℝ := (2:ℝ)^(-(1/8:ℝ))
def allowance:ℝ := ratio/(1-ratio)

theorem gap : 0 < ratio ∧ ratio < 1 :=
  ⟨Real.rpow_pos_of_pos (by norm_num) _,Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)⟩

theorem join (a b t:ℕ) : gain C a b*gain C b t=gain C a t := by
  rw [gain,gain,gain,←Real.exp_add];congr 1;ring

theorem total (b n:ℕ) : (∑ j∈Finset.range n,gain C (b+j) (b+n)) ≤ allowance := by
  have ag:0 ≤ allowance:=div_nonneg gap.1.le (sub_nonneg.mpr gap.2.le)
  induction n with
  | zero=>simpa only [Finset.range_zero,Finset.sum_empty] using ag
  | succ n ih=>
    let l:=factor C (b+n)^(-(1/8:ℝ))
    have hi:(2:ℕ) ≤ (C.S.block (b+n)).val:=by
      have h:(1:ℕ)<(C.S.block (b+n)).val:=by exact_mod_cast factor_positive C (b+n)
      exact h
    have hl:l ≤ ratio:=Real.rpow_le_rpow_of_nonpos (by norm_num)
      (show (2:ℝ)≤factor C (b+n) by exact_mod_cast hi) (by norm_num)
    have l0:0 ≤ l:=Real.rpow_nonneg (zero_lt_one.trans (factor_positive C (b+n))).le _
    calc
      _ = ((∑ j∈Finset.range n,gain C (b+j) (b+n))+1)*l := by
        rw [Finset.sum_range_succ,Nat.add_succ]
        simp_rw [gain_step]
        rw [gain_self,←Finset.sum_mul,add_mul,one_mul]
      _ ≤ (allowance+1)*ratio:=mul_le_mul (add_le_add ih (le_refl (1:ℝ))) hl l0 (by linarith only [ag])
      _ = allowance:=by unfold allowance;field_simp [(sub_pos.mpr gap.2).ne'];ring

/-- The prefix stops at its actual date k. No number of dates, regulator, or
box count occurs in the geometric constant. -/
theorem first_dates {b n k:ℕ} (earlier:k ≤ n) {ε B:ℝ} (ep:0 ≤ ε) (Bp:0 ≤ B) (a:ℕ→ℂ)
    (paid:∀ j<n,‖a j‖ ≤ ε*gain C (b+j) (b+n)*B) :
    (∑ j∈Finset.range k,‖a j‖) ≤ ε*B*gain C (b+k) (b+n)*allowance := by
  have pos:0 ≤ ε*B*gain C (b+k) (b+n):=mul_nonneg (mul_nonneg ep Bp) (Real.exp_pos _).le
  calc
    _ ≤ ∑ j∈Finset.range k,(ε*B*gain C (b+k) (b+n))*gain C (b+j) (b+k) := by
      apply Finset.sum_le_sum
      intro j hj
      apply (paid j ((Finset.mem_range.mp hj).trans_le earlier)).trans_eq
      rw [←join C (b+j) (b+k) (b+n)];ring
    _ = _ := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (total C b k) pos

end YM.Integration.WilsonOriginalNullUnitSum
