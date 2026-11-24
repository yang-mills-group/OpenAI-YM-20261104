import YM.Pert.Kinetic.Branch
set_option autoImplicit false
noncomputable section
namespace YM.Pert.Kinetic
open Function Filter Set Lattice Wilson RG
open scoped Topology BigOperators Classical ContDiff
variable {n : Side} {G : Gauge} {p : BudgetPoint} {σ C Λ δ s β u : ℝ}
structure Quotes (p : BudgetPoint) (σ C Λ δ s : ℝ) : Prop where
    pos : 1 ≤ s
    jump : 0< σ
    width : σ⁻¹ ≤ s
    paths : |C| ≤ s
    loop : Λ ≤ s
    price : δ ≤ s
    price_lo : 0 ≤ δ
    cover : (p.B:ℝ) ≤ s
    inv_support : p.supportExponent⁻¹ ≤ s
    inv_field : p.threshold⁻¹ ≤ s
lemma quotes_le {t:ℝ} (h :s≤t) (he : Quotes p σ C Λ δ s) : Quotes p σ C Λ δ t := by cases he; constructor <;> linarith

def up : ℝ := 2*Real.pi+2
def coefK : ℝ  := 2*(Fintype.card PlaqAxes:ℝ)+2+up*3+(600/(2*Real.pi))^3*18
lemma coefK_pos : 0 < coefK := by unfold coefK up;have hp:=Real.pi_pos;nlinarith [pow_nonneg (show 0≤(600/(2*Real.pi):ℝ) from by positivity) 3, Nat.cast_nonneg (α:=ℝ) (Fintype.card PlaqAxes)]
lemma freq_le (h : s ≥ 1) (n : ℕ)(m : ℕ)(hh:n ≤ m) : s^n ≤ s^m := pow_le_pow_right₀ h hh
lemma paid_quote (he : Quotes p σ C Λ δ s) (hu : 0 ≤ u) (h : |β| ≤ s+u) : billTotal p σ C Λ β δ ≤ coefK*s^9+2*(Fintype.card PlaqAxes)*s^9*u := by
   have hs:=he.pos; have hp:=Real.pi_pos
   have h1 : 0 ≤ windPrice σ C (max 0 Λ) β := by unfold windPrice rowCost; have := he.jump; positivity
   have hw : rowCost σ C ≤ s^3 := by
     calc
       _ ≤ s^2 * s := mul_le_mul (by change C^2 ≤ _; exact sq_abs C ▸ pow_le_pow_left₀ (abs_nonneg C) he.paths 2) he.width (inv_nonneg.mpr he.jump.le) (sq_nonneg _)
       _ = _ := by ring
   have hσ:=he.jump
   have hk : windPrice σ C Λ β ≤ 2*(s*((Fintype.card PlaqAxes)*s^3)+u*((Fintype.card PlaqAxes)*s^3)+s^2) := by
       calc _ = 2* (|β| * ((Fintype.card PlaqAxes : ℝ)*rowCost σ C)+ (Λ/σ)) := by unfold windPrice;ring
            _ ≤ 2*((s+u)*((Fintype.card PlaqAxes : ℝ)*s^3) + (s*s)) := mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul h (mul_le_mul_of_nonneg_left hw (Nat.cast_nonneg _)) (show 0 ≤ ((Fintype.card ..):ℝ)*rowCost σ C from by unfold rowCost; positivity) (by linarith)) (by rw [div_eq_mul_inv]; exact mul_le_mul he.loop he.width (inv_nonneg.mpr he.jump.le) (by linarith))) zero_le_two
            _ = _ := by ring
   have H : 100*(4*(p.B:ℝ)+2)/((2*Real.pi)*p.supportExponent) ≤ 600/(2*Real.pi)*s^2 := by
      have : 4*(p.B:ℝ)+2 ≤ 6*s := by linarith only [he.cover,hs]
      rw [div_mul_eq_div_div,div_eq_mul_inv _ p.supportExponent]
      refine (mul_le_mul (show _ ≤ (600/(2*Real.pi))*s from ?_) he.inv_support (inv_nonneg.mpr p.exponent_pos.le) (by positivity)).trans_eq (by ring)
      refine le_trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left this (show (0:ℝ) ≤ 100 by norm_num)) (by positivity : (0:ℝ) ≤ 2*Real.pi)) (le_of_eq (by ring)) -- RHS syntaxes
   have hE:= pow_le_pow_left₀ (by have :=p.exponent_pos; positivity) H 3
   have hf : geomE p ≤ s^2 * (up*3+(600/(2*Real.pi)*s^2)^3 * 18) := by
       unfold geomE; rw [one_div,← inv_pow]; refine mul_le_mul ?_ (add_le_add_right (mul_le_mul_of_nonneg_right hE (by norm_num : (0:ℝ) ≤ 18)) _) (by have:= p.exponent_pos; positivity) (sq_nonneg _)
       exact pow_le_pow_left₀ (inv_nonneg.mpr p.threshold_pos.le) he.inv_field 2
   have hCard:=Nat.cast_nonneg (α:=ℝ) (Fintype.card PlaqAxes)
   have H := add_le_add hk (mul_le_mul hf he.price he.price_lo (show 0≤_ from by unfold up; positivity)) -- hk.add fix
   unfold coefK; unfold billTotal
   have h0: 0 ≤ s:=zero_le_one.trans hs; have hU:(0:ℝ) ≤ up:= by unfold up;positivity
   nlinarith only [H, freq_le hs 2 9 (by decide), mul_le_mul_of_nonneg_left (freq_le hs 4 9 (by decide)) hCard, mul_le_mul_of_nonneg_left (freq_le hs 3 9 (by decide)) hU, mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (freq_le hs 3 9 (by decide)) hCard) hu]
end YM.Pert.Kinetic
