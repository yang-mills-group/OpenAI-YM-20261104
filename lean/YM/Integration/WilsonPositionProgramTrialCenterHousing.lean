import YM.Integration.WilsonPositionProgramTrialCellDigits

/-! An anchor reduced in the box of the true older site has physical
Euclidean norm at most the older spacing. All other sites keep exactly their
original relative displacements. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialCenterHousing
open Finset Function Lattice WilsonCoeffUV.Bank
open WilsonPositionProgramTrialCellDigits
open scoped BigOperators Classical
variable {I : Type*}

theorem grid_sub (S : Schedule) (f : ℕ) (a b : Cover) :
    S.gridPoint f (a-b) = S.gridPoint f a - S.gridPoint f b := by
  ext i
  simp [Schedule.gridPoint,mul_sub]

theorem anchor_bound (S : Schedule) {w f : ℕ} (cut : w ≤ f) (o : I → Cover) (a : I) :
    ‖S.gridPoint f (residual S cut o a a)‖ ≤ S.a w := by
  rw [pivot]
  let g := S.toDepth cut 0
  let x := wrap g.count (o a)
  have hs:=S.embeds_scale g
  have ha:=S.a_pos f
  have coords (i : Axis) : ‖S.gridPoint f (lift x) i‖ ≤ S.a w/2 := by
    have h:=lift_centers x i
    have lt : -(g.count.val:ℝ) < 2*((lift x i : ℤ):ℝ) := by exact_mod_cast h.1
    have le : (2:ℝ)*((lift x i : ℤ):ℝ) ≤ g.count.val := by exact_mod_cast h.2
    change |S.a f*((lift x i:ℤ):ℝ)| ≤ _
    rw [abs_le,←hs]
    constructor
    · nlinarith [mul_lt_mul_of_pos_left lt ha]
    · nlinarith [mul_le_mul_of_nonneg_left le ha.le]
  have total : ‖S.gridPoint f (lift x)‖^2 ≤ ∑ _ : Axis, (S.a w/2)^2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    exact Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (coords i) _
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] at total
  change ‖S.gridPoint f (lift x)‖ ≤ S.a w
  nlinarith [S.a_pos w, norm_nonneg (S.gridPoint f (lift x))]

theorem original (S : Schedule) {w f : ℕ} (cut : w ≤ f) (o : I → Cover) (a i : I) :
    ‖S.gridPoint f (residual S cut o a i)‖ ≤ S.a w+‖S.gridPoint f (o i-o a)‖ := by
  let z j := S.gridPoint f (residual S cut o a j)
  have rel : z i-z a=S.gridPoint f (o i-o a) := by
    rw [←relative S cut o a i a,grid_sub]
  have h:=norm_add_le (z a) (z i-z a)
  rw [add_sub_cancel ..] at h
  rw [←rel]
  exact h.trans (add_le_add (anchor_bound S cut o a) le_rfl)

end YM.Integration.WilsonPositionProgramTrialCenterHousing
