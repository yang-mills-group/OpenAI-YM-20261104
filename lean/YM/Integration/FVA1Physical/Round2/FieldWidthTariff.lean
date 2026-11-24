import YM.Integration.FVA1Physical.Round2.SpatialFieldPrice
import YM.MSbar.Mosaic.Box
import YM.MSbar.Geneva.Snow

/-! The shrinking native spatial width fits the actual cover size. Summing
all derivative addresses at this width costs only a subpower of the scale. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Filter Lattice RG MSbar MSbar.Mosaic MSbar.Heath Push.Uniform
open scoped BigOperators Topology

theorem eventual_field_width (q s:ℕ) {σ:ℝ} (pos:0 < σ) :
    ∀ᶠ x:ℝ in atTop,
      0 < αm x ∧ (((s:ℝ)+1)*αm x+2*αm x)*q*(6*(⌈hatW x⌉₊:ℝ)+2) ≤ σ := by
  let C:=((s:ℝ)+1+2)*(q:ℝ)
  have c0:0 ≤ C:=by dsimp only [C];positivity
  filter_upwards [Alto.broad.eventually_ge_atTop 1,Alto.broad.eventually_ge_atTop (14*C/σ)] with x hx budget
  let w:=hatW x
  have live:0 < w:=zero_lt_one.trans_le hx
  have hi:(⌈w⌉₊:ℝ) ≤ 2*w:=(Nat.ceil_lt_add_one live.le).le.trans (by linarith only [hx])
  have alpha:αm x=(w^3)⁻¹:=by unfold αm;rw [zpow_neg];rfl
  rw [alpha]
  refine ⟨inv_pos.mpr (pow_pos live 3),?_⟩
  have coeff:(((s:ℝ)+1)*(w^3)⁻¹+2*(w^3)⁻¹)*q=C*(w^3)⁻¹:=by dsimp only [C];ring
  rw [coeff]
  calc
    _ ≤ C*(w^3)⁻¹*(14*w) := mul_le_mul_of_nonneg_left (by linarith only [hi,hx]) (mul_nonneg c0 (inv_nonneg.mpr (pow_nonneg live.le _)))
    _ = (14*C)/(w^2) := by field_simp
    _ ≤ σ := (div_le_iff₀ (pow_pos live 2)).mpr (((div_le_iff₀ pos).mp budget).trans
      (by nlinarith only [mul_nonneg (mul_nonneg pos.le live.le) (sub_nonneg.mpr hx)]))

def wordSupportFare (G:Gauge) (q s:ℕ) (x:ℝ) : ℝ :=
  (1+2*(αm x)⁻¹)^s*(4*Fintype.card G.ColorIndex*countCost (αm x))^q

theorem support_fare_subpower (G:Gauge) (q s:ℕ) :
    Mosaic.Run atTop id (wordSupportFare G q s) 0 := by
  let w:=fun x:ℝ=>(hatW x)^3
  have rate:Mosaic.Run atTop id w 0:=Mosaic.Run.Ypow tendsto_id (Mosaic.Run.stanza tendsto_id) 3
  let cap:ℝ:=Real.exp 2*(Nat.factorial 6:ℝ)*2^4
  let color:ℝ:=4*Fintype.card G.ColorIndex
  have major:Mosaic.Run atTop id (fun x=>(1+2*w x)^s*(color*(cap*(w x)^6))^q) 0:=
    ((Mosaic.Run.token tendsto_id 1).addR tendsto_id (rate.mulK tendsto_id 2)|>.Ypow tendsto_id s).Ymul tendsto_id
      (((rate.Ypow tendsto_id 6).mulK tendsto_id cap|>.mulK tendsto_id color).Ypow tendsto_id q)
  apply major.cash
  filter_upwards [Alto.broad.eventually_ge_atTop 1] with x hx
  have wx:1 ≤ w x:=one_le_pow₀ hx
  have live:0 < w x:=zero_lt_one.trans_le wx
  have alpha:αm x=(w x)⁻¹:=by unfold αm;rw [zpow_neg];rfl
  have a0:0 < αm x:=alpha ▸ inv_pos.mpr live
  have small:αm x ≤ 1:=alpha ▸ inv_le_one_of_one_le₀ wx
  have cc:countCost (αm x) ≤ cap*(w x)^6:=by
    unfold countCost cap
    have exp:Real.exp (αm x*2) ≤ Real.exp 2:=Real.exp_monotone (by linarith only [small])
    rw [alpha] at exp
    rw [div_eq_mul_inv,alpha,inv_pow,inv_inv]
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right exp (Nat.cast_nonneg _)) (pow_nonneg live.le _)) (by norm_num : 0 ≤ (2:ℝ)^4)).trans_eq (by ring)
  have c0:0 ≤ color:=by dsimp only [color];positivity
  have paid:wordSupportFare G q s x ≤ (1+2*w x)^s*(color*(cap*(w x)^6))^q:=by
    unfold wordSupportFare
    have invA:(αm x)⁻¹=w x:=by rw [alpha,inv_inv]
    rw [invA]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by linarith only [live]) _)
    exact pow_le_pow_left₀ (mul_nonneg c0 (count_pos a0).le) (mul_le_mul_of_nonneg_left cc c0) q
  have nonneg:0 ≤ wordSupportFare G q s x:=by
    unfold wordSupportFare
    have b:0 < countCost (αm x):=count_pos a0
    positivity
  simpa only [abs_of_nonneg nonneg] using paid.trans (le_abs_self _)

end YM.Integration.FVA1Physical.Round2.Curvature
