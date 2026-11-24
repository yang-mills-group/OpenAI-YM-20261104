import YM.Integration.WilsonSeparatedPrefixCanonicalIncome

/-! One positive wallet for the original finite roster. The denominator
includes the full single-field gross and the genuine old wallet, once per seat. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixCanonicalWallet
open Finset
open scoped BigOperators Classical
variable {V:Type} [Fintype V]

def debit(w₀ A B:V → ℝ)(v:V):ℝ:=
  1+(w₀ v)⁻¹+8*((Fintype.card V:ℝ)+1)*(1+A v+B v)

def seat(w₀ A B:V → ℝ)(v:V):ℝ:=Real.sqrt ((debit w₀ A B v)⁻¹)

theorem original (w₀ A B:V → ℝ)(paid:∀v,0<w₀ v)(an:∀v,0≤A v)(bn:∀v,0≤B v):
    let w:=seat w₀ A B
    (∀v,0<w v) ∧ (∀v,w v^2≤w₀ v) ∧ (∀v,(w v^2)⁻¹=debit w₀ A B v) ∧
      (∑v,w v^2*A v)≤1/8 ∧ (∑v,w v^2*B v)≤1/8:=by
  intro w
  let L:=8*((Fintype.card V:ℝ)+1)
  have lp:0<L:=by dsimp [L];positivity
  have major(v):0<debit w₀ A B v:=by
    unfold debit
    have :=an v
    have :=bn v
    have :=paid v
    positivity
  have squared(v):w v^2=(debit w₀ A B v)⁻¹:=Real.sq_sqrt (inv_nonneg.mpr (major v).le)
  have coin(v):L*(1+A v+B v)≤debit w₀ A B v:=by
    change L*(1+A v+B v)≤1+(w₀ v)⁻¹+L*(1+A v+B v)
    have :=inv_pos.mpr (paid v)
    linarith
  have either (Y:V → ℝ)(hy:∀v,Y v≤1+A v+B v):
      (∑v,w v^2*Y v)≤1/8:=by
    have each(v):w v^2*Y v≤1/L:=by
      rw [squared,inv_mul_eq_div]
      exact (div_le_div_iff₀ (major v) lp).mpr (by
        have cash:=(mul_le_mul_of_nonneg_left (hy v) lp.le).trans (coin v)
        linarith [mul_comm (Y v) L])
    refine (sum_le_sum (fun v _=>each v)).trans ?_
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    change (Fintype.card V:ℝ)*(1/L)≤1/8
    rw [mul_one_div]
    apply (div_le_div_iff₀ lp (by norm_num : (0:ℝ)<8)).mpr
    dsimp [L]
    linarith
  refine ⟨fun v=>Real.sqrt_pos.mpr (inv_pos.mpr (major v)),fun v=>?_,fun v=>by rw [squared,inv_inv],
    either A (fun v=>by linarith [bn v]),either B (fun v=>by linarith [an v])⟩
  rw [squared]
  have cap:(w₀ v)⁻¹≤debit w₀ A B v:=by
    change (w₀ v)⁻¹≤1+(w₀ v)⁻¹+L*(1+A v+B v)
    have :=mul_nonneg lp.le (by linarith [an v,bn v]:0≤1+A v+B v)
    linarith
  simpa only [inv_inv] using (inv_le_inv₀ (major v) (inv_pos.mpr (paid v))).mpr cap

end YM.Integration.WilsonSeparatedPrefixCanonicalWallet
