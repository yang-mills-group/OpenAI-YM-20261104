import YM.RG08.Packets.Torus
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Group.Real

/-!
Finite-period absolute row and column sums of the exact native display.
The column statement uses the original rectangular translation law and
matches_back. Its factor counts output types only; the complete block
multiplicity must still be retained by the supplying cover column bill.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.NativeFiniteMatrixCosts
open Lattice Laurent Matrix Function Bloch
open Pert.Bulk RG08.Packets
open scoped BigOperators ENNReal Classical

private theorem fiber_norm_le {I J : Type*} [Fintype J]
    (g : I → J) (f : I → ℝ) :
    (∑ j : J, ‖∑' i : I, if g i = j then f i else 0‖ₑ) ≤
      ∑' i : I, ‖f i‖ₑ := by
  calc
    _ ≤ ∑ j : J, ∑' i : I, ‖if g i = j then f i else 0‖ₑ :=
      Finset.sum_le_sum (fun _ _ => enorm_tsum_le_tsum_enorm)
    _ = ∑' j : J, ∑' i : I, ‖if g i = j then f i else 0‖ₑ := by
      rw [tsum_fintype]
    _ = ∑' i : I, ∑' j : J, ‖if g i = j then f i else 0‖ₑ :=
      ENNReal.tsum_comm
    _ = ∑' i : I, ‖f i‖ₑ := by
      apply tsum_congr
      intro i
      rw [tsum_fintype]
      rw [Finset.sum_eq_single (g i)]
      · simp only [ite_true]
      · intro j _ hj
        rw [if_neg (Ne.symm hj), enorm_zero]
      · simp

variable {α β : Type} {c f L : Side}
    {K : Kernel α β} {M : Matrix (Co f α) (Co c β) ℝ} {p : ℝ}

/-- Periodizing an absolute row sum introduces no number-of-sites factor. -/
theorem row_sum_le [Fintype β]
    (hM : Matches K M) (hK : RowCost 0 L K p) (hp : 0 ≤ p)
    (x : Co f α) :
    (∑ y : Co c β, |M x y|) ≤ (Fintype.card β : ℝ) * p := by
  have hper (i : β) :
      (∑ y : Site c, ‖M x (y, i)‖ₑ) ≤ ENNReal.ofReal p := by
    have he (y : Site c) :
        M x (y, i) = display K c (lift x.1, x.2) (y, i) := by
      simpa only [wrap_lift] using (hM (lift x.1, x.2) (y, i)).symm
    simp_rw [he]
    change (∑ y : Site c,
      ‖∑' z : Cover, if wrap c z = y then K (lift x.1, x.2) (z, i) else 0‖ₑ) ≤ _
    have hfiber := fiber_norm_le (wrap c) (fun z => K (lift x.1, x.2) (z, i))
    have hcost : (∑' z : Cover, ‖K (lift x.1, x.2) (z, i)‖ₑ) ≤ ENNReal.ofReal p := by
      simpa only [bill, zero_mul, Real.exp_zero, mul_one,
        Real.enorm_eq_ofReal_abs] using hK (lift x.1, x.2) i
    convert hfiber.trans hcost using 1
    · rfl
    · apply Finset.sum_congr rfl
      intro y _
      congr 1
      apply tsum_congr
      intro z
      by_cases hz : wrap c z = y <;> simp [hz]
  have hall :
      (∑ y : Co c β, ‖M x y‖ₑ) ≤
        ENNReal.ofReal ((Fintype.card β : ℝ) * p) := by
    calc
      _ = ∑ y : Site c, ∑ i : β, ‖M x (y, i)‖ₑ := by
        rw [Fintype.sum_prod_type]
      _ = ∑ i : β, ∑ y : Site c, ‖M x (y, i)‖ₑ := Finset.sum_comm
      _ ≤ ∑ _i : β, ENNReal.ofReal p := Finset.sum_le_sum (fun i _ => hper i)
      _ = ENNReal.ofReal ((Fintype.card β : ℝ) * p) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  apply (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (Nat.cast_nonneg _) hp)).mp
  calc
    ENNReal.ofReal (∑ y : Co c β, |M x y|) =
        ∑ y : Co c β, ‖M x y‖ₑ := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun y _ => abs_nonneg (M x y))]
      simp only [Real.enorm_eq_ofReal_abs]
    _ ≤ _ := hall

/-- The exact rectangular transpose uses the actual column bill and period
relation. No row estimate is substituted for that column bill. -/
theorem column_sum_le [Fintype α]
    (hperiod : f.val = c.val * L.val)
    (hcity : city L K) (hM : Matches K M)
    (hK : ColCost 0 L K p) (hp : 0 ≤ p) (y : Co c β) :
    (∑ x : Co f α, |M x y|) ≤ (Fintype.card α : ℝ) * p := by
  have hrow : RowCost 0 1 (Function.swap K) p := by
    intro x i
    simpa only [Function.swap, zero_mul] using hK i x
  simpa only [Matrix.transpose_apply] using
    row_sum_le (matches_back hperiod hcity hM) hrow hp y

end YM.Integration.NativeFiniteMatrixCosts
end
