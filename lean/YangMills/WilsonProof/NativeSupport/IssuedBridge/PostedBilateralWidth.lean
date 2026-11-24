import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedBilateralFieldCutoff
set_option autoImplicit false
noncomputable section
namespace IssuedBridge.PostedBilateralWidth
open YM.Integration Function Filter Set Finset
open scoped Topology ContDiff Classical BigOperators
variable {E : ℕ→Type*} [∀ d,NormedAddCommGroup (E d)] [∀d,NormedSpace ℝ (E d)]
variable (a : ∀ d,ℕ→E d)

def size (d : ℕ) : ℝ := 1+∑n∈range (d+1),‖a d n‖
def scaled (d n : ℕ) : E d := (size a d)⁻¹ • a d n
def cap (n : ℕ) : ℝ := 1+∑ d∈range (n+1),‖scaled a d n‖
def width (n : ℕ) : ℝ := 2^(n+1)*(1+cap a n)+(n:ℝ)+1


theorem floor (n : ℕ) : (2:ℝ) ≤ width a n := by
  unfold width cap
  have h : (1:ℝ) ≤ 2^(n+1) := one_le_pow₀ (by norm_num)
  have hp : (0:ℝ) ≤ ∑ d ∈ range (n+1), ‖scaled a d n‖ := by positivity
  nlinarith [mul_nonneg (sub_nonneg.mpr h) hp, Nat.cast_nonneg (α:=ℝ) n]

theorem original (d n : ℕ) (dn : d ≤ n) :
    ‖a d n‖ * (2:ℝ)^n ≤ size a d * width a n := by
  have pos : 0 < size a d := by unfold size; positivity
  have sub : ‖scaled a d n‖ ≤ ∑ i ∈ range (n+1), ‖scaled a i n‖ :=
    single_le_sum (f:=fun i => ‖scaled a i n‖) (fun i _ => norm_nonneg _) (Finset.mem_range.mpr (by omega))
  have room : ‖scaled a d n‖ ≤ cap a n := by unfold cap; linarith
  rw [scaled,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr pos.le),← div_eq_inv_mul] at room
  have income := (div_le_iff₀ pos).mp room
  have hit : (2:ℝ)^n * cap a n ≤ width a n := by
    have capPos : 0 ≤ cap a n := by unfold cap; positivity
    calc
      (2:ℝ)^n * cap a n ≤ 2^n * (1+cap a n) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ ≤ 2^(n+1) * (1+cap a n) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (Nat.le_succ n)) (by positivity)
      _ ≤ width a n := by unfold width; linarith [Nat.cast_nonneg (α:=ℝ) n]
  calc
    ‖a d n‖ * (2:ℝ)^n ≤ (cap a n * size a d) * 2^n := mul_le_mul_of_nonneg_right income (by positivity)
    _ = size a d * (2^n * cap a n) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hit pos.le
end IssuedBridge.PostedBilateralWidth
