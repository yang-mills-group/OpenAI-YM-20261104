import YM.Integration.WilsonOriginalNullPrimaryFees

/-! Absorb the canonical source, including its restored engineering weight,
using only its original wrapping bill and prices on the elected physical calendar. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalNullWrappedFee
open Filter Labels Lattice Wilson RG Source Trace.Physical Trace.Physical.Germ
open PhysicalNext Repeat Legato Graces Roost Org Push.Local Extra.Histories Next.Foundations
open scoped Classical Topology

variable {G:Gauge} (R:Run G) (d:ℕ)
local notation "F₀" => R.family.labels.level d
local notation "T₀" => R.family.localSection d
local notation "B₀" j:max => R.family.path.levels.budget j
local notation "w₀" j:max => price G (max (B₀ j).order (B₀ j).power)
local notation "staff₀" j:max => factor R.family.params T₀ (B₀ j).supportExponent (w₀ j)
local notation "forecast₀" j:max => R.family.path.levels.clock.hatBeta j
local notation "scale₀" j:max => R.family.S.scale j
local notation "block₀" j:max => GermGraph.factor R.family j
local notation "stock₀" j:max => 2 + 4*(R.family.path.levels.params j).columns
local notation "wrapCost" => (germ_close F₀ R.family.params).choose
local notation "slope" => (-((d:ℝ)+6))

theorem original (M:WilsonMeasuredRankedMenu.Menu R d) :
    ∀ᶠ i:ℕ in atTop, ∀ (per:ℕ) (o:Site (R.family.side (i+1) per)) (v:(F₀).Coeff) (a:ℝ),
    0 ≤ a → ‖v‖ ≤ wrapCost*Real.exp (slope*scale₀ (i+1))*a →
    let fee:=(block₀ i)^d * (4*staff₀ i+1) *
      (B₀ (i+1)).mass ((T₀).footprint o) (w₀ (i+1)*(F₀).coeffSize v)
    4*(stock₀ i)*fee  ≤  (block₀ i)^(-(1/8:ℝ))*a := by
  let H:=|R.family.path.levels.clock.bar|+|G.slopeConstant|+1
  let A:=M.cost*H
  let D:=(F₀).extra+1
  let X:=(4*A+1)*A*(D:ℝ)*(abs wrapCost)
  have hA : 0 ≤ A := by dsimp [A,H];have := M.positive;positivity
  have hX : 0 ≤ X := by dsimp [X];positivity
  have late:=R.family.S.divergent.eventually_ge_atTop X
  filter_upwards [late,eventually_ge_atTop M.onset,WilsonOriginalNullStock.original R.family] with i eligible on stock per o v a ha hv
  intro fee
  let s:=scale₀ (i+1)
  let t:=Real.exp s
  let l:=block₀ i
  have monotone := (OPE.scale_mono R.family.S).monotone (Nat.le_succ i)
  have s0 : 0 ≤ s := hX.trans (eligible.trans monotone)
  have t1 : 1 ≤ t:=Real.one_le_exp s0
  have tpos : 0<t:=Real.exp_pos _
  have xfit : X ≤ t := by
    have h:=Real.add_one_le_exp s
    linarith only [eligible.trans monotone,h]
  have lpos : 0<l:=(Nat.cast_pos.mpr (R.family.S.block i).pos)
  have l1 : 1 ≤ l:=by change (1:ℝ) ≤ ((R.family.S.block i).val:ℝ);exact_mod_cast (show 1 ≤ (R.family.S.block i).val from (R.family.S.block i).pos)
  have col : 0 ≤ (stock₀ i) := by linarith [(R.family.path.levels.params i).columns_ge]
  have inv : l⁻¹  ≤  l^(-(2/5:ℝ)) := by
    rw [←Real.rpow_neg_one];apply Real.rpow_le_rpow_of_exponent_le l1;norm_num
  have slow : l^(-(1/8:ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos l1 (by norm_num)
  have crude := (mul_le_mul_of_nonneg_left inv (mul_nonneg zero_le_four col)).trans (stock.trans slow)
  rw [←div_eq_mul_inv,div_le_iff₀ lpos,one_mul] at crude
  have f1:=WilsonOriginalNullPrimaryFees.forecast R i
  have f2:=(WilsonOriginalNullPrimaryFees.forecast R (i+1)).1
  have hH:0 ≤ H:=by dsimp [H];positivity
  have coarse : forecast₀ i  ≤  H*t:= f1.1.trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr monotone) hH)
  have price : 4*(staff₀ i)+1  ≤  (4*A+1)*t := by
    have z:=(WilsonOriginalNullPrimaryFees.slots R d M i on o).1
    have h:=z.trans (mul_le_mul_of_nonneg_left coarse M.positive.le)
    dsimp only [A]
    linarith only [h,t1]
  have roster : (B₀ (i+1)).mass ((T₀).footprint o) (w₀ (i+1))  ≤  A*t := by
    have z:=(WilsonOriginalNullPrimaryFees.slots R d M (i+1) (Nat.le_succ_of_le on) o).2
    exact z.trans ((mul_le_mul_of_nonneg_left f2 M.positive.le).trans_eq (mul_assoc _ _ _).symm)
  have σv : (F₀).coeffSize v ≤ (D:ℝ)*‖v‖ := by
    simpa only [D,Nat.cast_add,Nat.cast_one] using size_le_norm (F₀) v
  have decay : Real.exp (slope*s)= (t^(d+6))⁻¹ := by
    simp only [t, ← Real.exp_nat_mul,←Real.exp_neg,Nat.cast_add,Nat.cast_ofNat]
    congr 1;ring
  have val : (F₀).coeffSize v  ≤  (D:ℝ)*(abs wrapCost)*(t^(d+6))⁻¹*a := by
    rw [←decay]
    have h:=mul_le_mul_of_nonneg_right (le_abs_self wrapCost) (Real.exp_pos (slope*s)).le
    have bv:=hv.trans (mul_le_mul_of_nonneg_right h ha)
    exact σv.trans ((mul_le_mul_of_nonneg_left bv (Nat.cast_nonneg D)).trans_eq (by ring))
  have wallet : (B₀ (i+1)).mass ((T₀).footprint o) (w₀ (i+1)*(F₀).coeffSize v) =
      (B₀ (i+1)).mass ((T₀).footprint o) (w₀ (i+1))*(F₀).coeffSize v := by unfold BudgetPoint.mass;ring
  have rate : 0 ≤ staff₀ i:=mul_nonneg (Real.exp_pos _).le
    (zero_le_one.trans (atomPrice_ge_one R.family.params F₀ (zero_le_one.trans (price_one_le G _))))
  have mass0 : 0 ≤ (B₀ (i+1)).mass ((T₀).footprint o) (w₀ (i+1)) :=
    mul_nonneg (Real.exp_pos _).le (zero_le_one.trans (price_one_le G _))
  have y0 : 0 ≤ (F₀).coeffSize v := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  change 4*(stock₀ i)*(l^d*(4*(staff₀ i)+1)*_) ≤ _
  rw [wallet]
  calc
    _  ≤  t*(t^d*((4*A+1)*t)*((A*t)*((D:ℝ)*(abs wrapCost)*(t^(d+6))⁻¹*a))) := by
      apply mul_le_mul (crude.trans f1.2) _ (by positivity) tpos.le
      apply mul_le_mul (mul_le_mul (pow_le_pow_left₀ lpos.le f1.2 d) price (by linarith only [rate]) (by positivity)) _ (mul_nonneg mass0 y0) (by positivity)
      exact mul_le_mul roster val y0 (mul_nonneg hA tpos.le)
    _ = X/(t^3)*a := by
      dsimp only [X];rw [pow_add];field_simp [tpos.ne']
    _  ≤  t⁻¹*a := by
      apply mul_le_mul_of_nonneg_right _ ha
      rw [div_le_iff₀ (pow_pos tpos 3)]
      calc
        _  ≤  t^2 := xfit.trans (le_self_pow₀ t1 (by norm_num))
        _ = _ := by field_simp [tpos.ne']
    _  ≤  (block₀ i)^(-(1/8:ℝ))*a := by
      apply mul_le_mul_of_nonneg_right _ ha
      refine (inv_anti₀ lpos f1.2).trans ?_
      rw [←Real.rpow_neg_one];apply Real.rpow_le_rpow_of_exponent_le l1;norm_num

end YM.Integration.WilsonOriginalNullWrappedFee
