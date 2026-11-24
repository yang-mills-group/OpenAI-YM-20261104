import YM.MSbar.Mosaic.Cue

/-! A source with a subpower rooted budget can use the same two reserve orders
as the mixed physical comparison at the preceding scale. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Filter MSbar MSbar.Mosaic MSbar.Heath.Stock
open scoped Topology

theorem reclocked_two_reserve (p : ℕ) (M : ℝ) (hM : 0 ≤ M) {η : ℝ}
    (hη : 0 < η) (hp : η < (p:ℝ)+1) :
    ∀ᶠ y : ℝ in atTop, ∀ g : ℝ, lensT y g →
      y^(1/4:ℝ)*y^(pawn (p+2)) + M*y^(-((p+2:ℕ):ℝ)) + 2*g^(p+1)*y^(η/8) ≤
        g^((p:ℝ)+1-η) := by
  let α : ℝ := (p:ℝ)+1-η
  let a : ℝ := -(1/2:ℝ)*((p+1:ℕ):ℝ)+η/8
  let b : ℝ := -(1/2:ℝ)*α
  let C : ℝ := 1+M+2*(2:ℝ)^(p+1)
  have pos : 0 < α := sub_pos.mpr hp
  have ab : a < b := by dsimp [a,b,α];push_cast;linarith only [hη]
  have c1 : (1/4:ℝ)+pawn (p+2) ≤ a := by unfold pawn;dsimp [a];push_cast;linarith only [hη]
  have c2 : -((p+2:ℕ):ℝ) ≤ a := by dsimp [a];push_cast;linarith only [hη,Nat.cast_nonneg (α:=ℝ) p]
  have receives := (tendsto_rpow_atTop (sub_pos.mpr ab)).eventually_ge_atTop ((2:ℝ)^α*C)
  filter_upwards [eventually_ge_atTop (1:ℝ),receives] with y large cap
  intro g band
  have hy := zero_lt_one.trans_le large
  have cq : 0 < cue y := inv_pos.mpr (Real.sqrt_pos.mpr hy)
  have hg := (half_pos cq).trans_le band.1
  have same : cue y = y^(-(1/2:ℝ)) := by rw [Real.rpow_neg hy.le,←Real.sqrt_eq_rpow];rfl
  have tail : g^(p+1)*y^(η/8) ≤ (2:ℝ)^(p+1)*y^a := by
    calc
      _ ≤ (2*cue y)^(p+1)*y^(η/8) := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ hg.le band.2 _) (Real.rpow_nonneg hy.le _)
      _ = _ := by rw [mul_pow,same,← Real.rpow_natCast (y^(-(1/2:ℝ))),
            ←Real.rpow_mul hy.le,mul_assoc,←Real.rpow_add hy]
  have fee : y^(1/4:ℝ)*y^(pawn (p+2))+M*y^(-((p+2:ℕ):ℝ))+2*g^(p+1)*y^(η/8) ≤ C*y^a := by
    have w:=Real.rpow_le_rpow_of_exponent_le large c1
    rw [Real.rpow_add hy] at w
    have v := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le large c2) hM
    dsimp only [C]
    linarith only [w,v,tail]
  have up : C*y^a ≤ g^α := by
    apply (mul_le_mul_iff_right₀ (Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) α)).mp
    calc
      (2:ℝ)^α*(C*y^a) ≤ y^(b-a)*y^a := by rw [←mul_assoc];exact mul_le_mul_of_nonneg_right cap (Real.rpow_nonneg hy.le _)
      _ = y^b := by rw [←Real.rpow_add hy,sub_add_cancel]
      _ = (cue y)^α := by rw [same,←Real.rpow_mul hy.le]
      _ ≤ (2*g)^α := Real.rpow_le_rpow cq.le (by linarith only [band.1]) pos.le
      _ = (2:ℝ)^α*g^α := Real.mul_rpow (by norm_num) hg.le
  exact fee.trans up

end YM.Integration.FVA1Physical.Round2.Curvature
