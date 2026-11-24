import YM.Integration.WilsonTrueProjectedSignedLedger

/-! A finite reporting window costs one power of its mesh ratio for the
number of receiving dates. The original measured frame costs d+1 powers. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonTrueProjectedWindowPrice
open Function Finset Lattice Wilson RG Labels Source Trace.Physical Trace.Physical.GermGraph
open Extra.Histories PhysicalNext Repeat Legato
open scoped Classical Matrix.Norms.Frobenius
variable {G : Gauge} (C : Family G) {d m j N p stop : ℕ}
local notation "σ" => (C.labels.level d).coeffSize
local notation "X" => measuring C d N p

theorem dates (h : m ≤ j) : ((j-m : ℕ) : ℝ) + 1 ≤ C.S.a m/C.S.a j := by
  induction j,h using Nat.le_induction with
  | base => simp [(C.S.a_pos m).ne']
  | succ i hmi ih =>
    have length : i+1-m = (i-m)+1 := by omega
    have ratio : 1 ≤ C.S.a m/C.S.a i :=
      (one_le_div (C.S.a_pos i)).mpr (C.S.strictAnti.antitone hmi)
    have large : (2:ℝ) ≤ (C.S.block i).val := by exact_mod_cast (show 2≤(C.S.block i).val by
      have := C.S.block_large i; omega)
    have scale : C.S.a m/C.S.a (i+1) = (C.S.a m/C.S.a i)*(C.S.block i).val := by
      rw [C.S.a_step,div_div_eq_mul_div,div_mul_eq_mul_div]
    rw [length,Nat.cast_add,Nat.cast_one,scale]
    linarith only [ih,ratio,mul_le_mul_of_nonneg_left large (zero_le_one.trans ratio)]

theorem original (H : C.Makes) (hm : Opened C d m p) (range : m ≤ stop) (live : stop ≤ N)
    (ready : ∀ i ≥ m, i < stop → Opened C d i p)
    (path : ℕ → C.label d) (D : ℝ) (positive : 0 ≤ D)
    (budget : ∀ i ≥ m, i < stop → σ (X i (path (i+1)) - X i (path i)) ≤ D) :
    σ (X m (path stop) - X m (path m)) ≤ 4*(C.S.a m/C.S.a stop)^(d+2)*D := by
  let r := C.S.a m/C.S.a stop
  have rp : 0 ≤ r := div_nonneg (C.S.a_pos _).le (C.S.a_pos _).le
  have times : ((stop-m : ℕ) : ℝ) ≤ r := by linarith only [dates C range]
  have accrued := (WilsonTrueProjectedSignedLedger.signed C H hm range live ready path (fun _ => D) budget).2
  apply accrued.trans
  calc
    _ ≤ ∑ _ : Fin (stop-m), 4*r^(d+1)*D := by
      apply Finset.sum_le_sum
      intro t _
      have high : m+t.val ≤ stop := by omega
      have paid := div_le_div_of_nonneg_left (C.S.a_pos m).le (C.S.a_pos stop) (C.S.strictAnti.antitone high)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (div_nonneg (C.S.a_pos m).le (C.S.a_pos _).le) paid (d+1)) (by norm_num)) positive
    _ = ((stop-m : ℕ) : ℝ)*(4*r^(d+1)*D) := by simp [nsmul_eq_mul]
    _ ≤ r*(4*r^(d+1)*D) := mul_le_mul_of_nonneg_right times (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg rp _)) positive)
    _ = _ := by change r*(4*r^(d+1)*D) = 4*r^(d+1+1)*D; rw [pow_succ r (d+1)]; ring

end YM.Integration.WilsonTrueProjectedWindowPrice
