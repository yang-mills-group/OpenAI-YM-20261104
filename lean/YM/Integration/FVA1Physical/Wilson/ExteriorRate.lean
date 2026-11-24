import YM.Integration.FVA1Physical.Wilson.RootedToll

/-! The exponential factor at the actual `boxX` boundary dominates every
fixed polynomial growth of the whole Wilson bank and the rescaled background. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter Finset MSbar MSbar.Whisk MSbar.Mosaic MSbar.Mosaic.Issue MSbar.Heath.Stock
open scoped Classical Topology

theorem exterior_toll (m s : ℕ) (C b Q : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ y : ℝ in atTop,
      2*(C*y)*(y^b*(1+3*(C*y))^(m+1)) / liftW (αm y) s (spotN y) ≤ y^(-Q) := by
  have unit : Mosaic.Run atTop id id 1 :=
    (Mosaic.Run.core (X:=id) tendsto_id 1).alter (Eventually.of_forall fun y=>Real.rpow_one y)
  have k := unit.mulK tendsto_id C
  have growth := (((Mosaic.Run.token (X:=id) tendsto_id 1).loosen (zero_le_one)).addR tendsto_id
    (k.mulK tendsto_id 3)).raise tendsto_id (m+1)
  have poly := (k.mulK tendsto_id 2).mulR tendsto_id ((Mosaic.Run.core (X:=id) tendsto_id b).mulR tendsto_id growth)
  have decay := (Mosaic.Issue.nearB (X:=id) tendsto_id 1 zero_lt_one 0 0).1
  have van := Mosaic.Van.mulL tendsto_id poly decay
  filter_upwards [van (-Q-1) (-Q) (by linarith),eventually_ge_atTop (1:ℝ)] with y hy y1
  let U:=2*(C*y)*(y^b*(1+3*(C*y))^(m+1))
  let a:=αm y
  let L:=spotN y
  have a0 : 0 ≤ a := zpow_nonneg (sq_nonneg _) _
  have th : thorn y 0 ≤ a := by
    change a / ((0+10:ℕ):ℝ) ≤ a
    norm_num
    linarith
  have exp : Real.exp (thorn y 0*L) ≤ liftW a s L := by
    refine (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right th (Nat.cast_nonneg _))).trans ?_
    exact le_mul_of_one_le_left (Real.exp_pos _).le (one_le_pow₀ (le_add_of_nonneg_right (Nat.cast_nonneg L) : (1:ℝ) ≤ 1+(L:ℝ)))
  have y0 : 0 ≤ y := zero_le_one.trans y1
  have posU : 0 ≤ U := by dsimp [U]; positivity
  calc U/liftW a s L ≤ U/Real.exp (thorn y 0*L) := div_le_div_of_nonneg_left posU (Real.exp_pos _) exp
       _ = Real.exp (-thorn y 0*L)*U := by rw [neg_mul,Real.exp_neg,div_eq_mul_inv,mul_comm]
       _ ≤ _ := (le_abs_self _).trans hy

theorem inverse_clock_le_linear {y g : ℝ} (hy : 1 ≤ y) (band : lensT y g) :
    0 < g ∧ |g⁻¹| ≤ 2*y := by
  have y0 := zero_lt_one.trans_le hy
  have sq0 := Real.sqrt_pos.mpr y0
  have halfpos := half_pos (inv_pos.mpr sq0)
  have g0 : 0 < g := halfpos.trans_le band.1
  refine ⟨g0,?_⟩
  rw [abs_of_pos (inv_pos.mpr g0)]
  have inv := inv_anti₀ halfpos band.1
  change g⁻¹ ≤ _ at inv
  have scale : (cue y / 2)⁻¹ = 2*Real.sqrt y := by
    unfold cue
    field_simp
  have sq1 : 1 ≤ Real.sqrt y := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hy
  exact (inv.trans_eq scale).trans (mul_le_mul_of_nonneg_left
    (by nlinarith [Real.sq_sqrt y0.le, mul_nonneg (sub_nonneg.mpr sq1) (Real.sqrt_nonneg y)] : Real.sqrt y ≤ y) zero_le_two)

end YM.Integration.FVA1Physical.Wilson
