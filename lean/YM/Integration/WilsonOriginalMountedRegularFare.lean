import YM.Integration.WilsonOriginalPhysicalCorridorPrecision

/-! Elect a support crop logarithmic in the original coupling after all fixed restoration debts. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalMountedRegularFare
open scoped Classical BigOperators

def crop (q:ℕ)(g:ℝ):ℕ:=⌈(q:ℝ)*Real.log g⁻¹⌉₊

theorem exponential (q h:ℕ){g α:ℝ}(pos:0<g)(width:1 ≤ α)(cut:crop q g ≤ h):
    (Real.exp (α*h))⁻¹ ≤ g^q:=by
  have threshold:(q:ℝ)*Real.log g⁻¹ ≤ h:=(Nat.le_ceil _).trans (by exact_mod_cast cut)
  have tall:(h:ℝ) ≤ α*h:=le_mul_of_one_le_left (by positivity) width
  calc
    _ = Real.exp (-(α*h)):=(Real.exp_neg _).symm
    _ ≤ Real.exp (-((q:ℝ)*Real.log g⁻¹)):=Real.exp_le_exp.mpr (neg_le_neg (threshold.trans tall))
    _ = Real.exp ((q:ℝ)*Real.log g):=by congr 1;rw [Real.log_inv];ring
    _ = _:=by rw [Real.exp_nat_mul,Real.exp_log pos]

theorem restore {g a b:ℝ}(d q:ℕ)(pos:0<g)(bp:0 ≤ b)(large:a ≤ (g^d)⁻¹)(paid:b ≤ g^(q+d)):
    a*b ≤ g^q:=by
  have due:=mul_le_mul large paid bp (inv_nonneg.mpr (pow_nonneg pos.le d))
  calc
    _ ≤ (g^d)⁻¹*g^(q+d):=due
    _ = g^q:=by rw [pow_add];field_simp

theorem small (q w d h:ℕ){g W rent gross δ α:ℝ}(pos:0<g)(cold:3*g ≤ 1)(width:1 ≤ α)
    (cut:crop (q+1+w+d) g ≤ h)(wallet:W ≤ (g^w)⁻¹)(size:gross ≤ (g^d)⁻¹)
    (np:0 ≤ rent)(sp:0 ≤ gross)(old:rent ≤ g^(q+1+w))(signed:δ ≤ g^(q+1)):
    W*rent+W*((Real.exp (α*h))⁻¹*gross)+δ ≤ g^q:=by
  have short:=exponential (q+1+w+d) h pos width cut
  have oldFee:=restore w (q+1) pos np wallet old
  have reverse:=restore d (q+1+w) pos (inv_nonneg.mpr (Real.exp_nonneg (α*h))) size short
  have raw:(Real.exp (α*h))⁻¹*gross ≤ g^(q+1+w):=by simpa only [mul_comm gross] using reverse
  have tail:=restore w (q+1) pos (mul_nonneg (inv_nonneg.mpr (Real.exp_nonneg (α*h))) sp) wallet raw
  calc
    _ ≤ g^(q+1)+g^(q+1)+g^(q+1):=add_le_add (add_le_add oldFee tail) signed
    _ = (3*g)*g^q:=by rw [pow_succ];ring
    _ ≤ g^q:=by simpa only [one_mul] using mul_le_mul_of_nonneg_right cold (pow_nonneg pos.le q)

end YM.Integration.WilsonOriginalMountedRegularFare
end
