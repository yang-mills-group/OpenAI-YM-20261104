import YM.Pert.Kinetic.Actual
set_option quotPrecheck false
set_option autoImplicit false
noncomputable section
namespace YM.Pert.Kinetic
open Function Filter Set Lattice Wilson RG MeasureTheory Asymptotics Bid Source
open Work.F03
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge} (C:Family G) (hG:G.Simple)
include hG
local notation "A" => C.path.levels
local notation "P" => (A).clock
/-- Superpower mesh accuracy is uniform even at varying physical volume. -/
lemma stay (q:ℕ) (K:ℝ) : ∀ᶠ i : ℕ in atTop, ∀ z:ℕ, (2*((P).hatBeta i))^q * |K| * Full.mesh (C.side i z) ≤ 1 := by
    let S:=C.S; let H: ℕ → ℝ := (P).hatBeta
    let D:= (P).bar+G.slopeConstant
    have h1 : Tendsto (fun i:ℕ=> (S.scale i)^q * S.a i) atTop (𝓝 0) := by
       convert (isLittleO_pow_exp_pos_mul_atTop q (b:=1) zero_lt_one).tendsto_div_nhds_zero.comp C.S.divergent using 1
       funext; rw [Stock.a_log,Real.exp_neg,comp_apply,div_eq_mul_inv,one_mul]
    have h2:= (h1.const_mul ((2*D)^q)) |>.mul_const |K| |>.mul_const (2*Real.pi)
    rw [mul_zero,zero_mul,zero_mul] at h2
    filter_upwards [h2.eventually_le_const zero_lt_one,S.divergent.eventually_ge_atTop 1] with i hi hS z
    change (2*H i)^q * |K| *Full.mesh (S.side i z) ≤ _
    apply le_trans ?_ hi
    have h3 : Full.mesh (S.side i z) ≤ 2*Real.pi*S.a i := by
       apply (div_le_iff₀ (Full.val_pos ..)).2; rw [mul_assoc,Schedule.span_side]; exact le_mul_of_one_le_right (by positivity) (by exact_mod_cast (S.period z).pos)
    have ht:0 ≤ H i:= (zero_lt_one.trans ((A).fits.delayed i)).le
    change _ ≤ (2*D)^q * (S.scale i ^ q * S.a i ) * |K| *(2*Real.pi)
    calc _ ≤ ((2*D)*S.scale i)^q * |K| * (2*Real.pi * S.a i) := by
            have hm:= Full.mesh_pos (n:= S.side i z); have hD:0≤D:=add_nonneg (P).bar_pos.le (G.slopeConstant_pos hG).le
            have hY : (2*H i)≤ (2*D)*S.scale i:= by unfold H Calendar.hatBeta D; change _ ≤ _ ; have hw:= mul_le_mul_of_nonneg_left hS (P).bar_pos.le; dsimp only [S] at *; unfold Family.S; linarith only [hw]
            exact mul_le_mul (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (mul_nonneg zero_le_two ht) hY q) (abs_nonneg K)) h3 hm.le (by positivity)
         _ = _ := by rw [mul_pow]; ring

end YM.Pert.Kinetic
