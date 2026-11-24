import YM.Integration.FVA1Physical.Round2.FieldRootedComparison
import YM.Integration.FVA1Physical.Round2.FieldReserveClock
import YM.Integration.FVA1Physical.Round2.FieldWidthTariff

/-! A finite order reserve pays the spatial sum at the measured physical
coupling. The interaction order at which the pointwise comparison is used
depends only on the requested final order. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Filter Function Lattice RG MSbar MSbar.Heath MSbar.Mosaic Push.Uniform
open scoped Topology BigOperators
def rootedChartWidth (q : ℕ) (x : ℝ) := αm x / ((q:ℝ)+2)

theorem field_kernel_subpower (G : Gauge) (q : ℕ) :
    Mosaic.Run atTop id (fun x => (fieldKernel G (rootedChartWidth q x))^q) 0 := by
  let w := fun x : ℝ => ((q:ℝ)+2)*(hatW x)^3
  have price : Mosaic.Run atTop id w 0 :=
    ((Mosaic.Run.stanza tendsto_id).Ypow tendsto_id 3).mulK tendsto_id ((q:ℝ)+2)
  let C := (Fintype.card (Exterior.TypeFace 1)*(Fintype.card G.ColorIndex:ℝ))*meter 1
  let v := fun x => 2*w x+3
  have sub : Mosaic.Run atTop id v 0 := (price.mulK tendsto_id 2).addR tendsto_id (Mosaic.Run.token tendsto_id 3)
  have major := (((sub.Ypow tendsto_id 4).mulK tendsto_id C).Ypow tendsto_id q)
  apply major.cash
  filter_upwards [Alto.broad.eventually_ge_atTop 1] with x hx
  have positive : 0 < hatW x := zero_lt_one.trans_le hx
  have factor : 0 < (q:ℝ)+2 := by positivity
  have invA : (rootedChartWidth q x)⁻¹ = w x := by
    unfold rootedChartWidth αm w
    rw [inv_div,zpow_neg]
    change ((q:ℝ)+2)/((hatW x)^3)⁻¹ = ((q:ℝ)+2)*(hatW x)^3
    rw [div_eq_mul_inv,inv_inv]
    rfl
  have w0 : 0 ≤ w x := by dsimp only [w]; positivity
  have hi : 2*(⌈(rootedChartWidth q x)⁻¹⌉₊:ℝ)+1 ≤ v x := by
    rw [invA]
    have le := (Nat.ceil_lt_add_one w0).le
    dsimp only [v]
    linarith only [le]
  have meter0 : 0 ≤ meter 1 := (meter_pos zero_lt_one).le
  have cap0 : 0 ≤ C := by dsimp only [C]; positivity
  have bill : fieldKernel G (rootedChartWidth q x) ≤ C*(v x)^4 := by
    unfold fieldKernel C
    rw [←mul_assoc, mul_right_comm _ (meter 1)]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hi 4) (by positivity)) meter0
  have value0 : 0 ≤ fieldKernel G (rootedChartWidth q x) := by unfold fieldKernel; positivity
  refine (le_of_eq (abs_of_nonneg (pow_nonneg value0 q))).trans ?_
  exact (pow_le_pow_left₀ value0 bill q).trans (le_abs_self _)

theorem summed_field_clock (p : ℕ) (C : ℝ) (hC : 0 ≤ C) {η : ℝ} (hη : 0 < η) :
    let d := p+8
    let P := p+d
    ∀ᶠ β : ℝ in atTop, ∀ x : ℝ, 1 ≤ x → x ≤ 2*β →
      let g := (Real.sqrt β)⁻¹
      let H := x^(rowExponent η)
      let τ := g^(p+4)
      τ*(β+(((P+1:ℕ):ℝ)*H)*C) + (g^P/τ)*β + ((d:ℝ)*g^(p+1)*H)*C ≤ g^((p:ℝ)+1-η) := by
  intro d P
  let base := 2+((P+1:ℕ):ℝ)*C
  obtain ⟨_,clock⟩ := derivative_clock p base ((d:ℝ)*C) (mul_nonneg (Nat.cast_nonneg _) hC) hη
  filter_upwards [clock,eventually_ge_atTop (1:ℝ)] with β budget hβ x hx upper
  intro g H τ
  have gp : 0 < g := inv_pos.mpr (Real.sqrt_pos.mpr (zero_lt_one.trans_le hβ))
  have unit : g ≤ 1 := inv_le_one_of_one_le₀ (Real.one_le_sqrt.mpr hβ)
  have mult : g^2*β = 1 := by
    dsimp only [g]
    rw [inv_pow,Real.sq_sqrt (zero_le_one.trans hβ),inv_mul_cancel₀ (zero_lt_one.trans_le hβ).ne']
  have pβ : τ*β ≤ g^(p+1) := by
    calc τ*β = g^(p+2)*(g^2*β) := by dsimp only [τ];rw [←mul_assoc,←pow_add]
         _ = g^(p+2) := by rw [mult,mul_one]
         _ ≤ g^(p+1) := pow_le_pow_of_le_one gp.le unit (by omega)
  have same : g^P/τ = g^(p+4) := by
    have eqn : P=(p+4)+(p+4) := by dsimp only [P,d];omega
    rw [eqn,pow_add]
    exact mul_div_cancel_right₀ _ (pow_pos gp _).ne'
  obtain ⟨HB,final⟩ := budget x hx upper
  have main : τ*(β+(((P+1:ℕ):ℝ)*H)*C) ≤ (1+((P+1:ℕ):ℝ)*C)*g^(p+1) := by
    have hK : 0 ≤ ((P+1:ℕ):ℝ)*C := mul_nonneg (Nat.cast_nonneg _) hC
    have front : τ*(H*(((P+1:ℕ):ℝ)*C)) ≤ g^(p+1)*(((P+1:ℕ):ℝ)*C) := by
      rw [←mul_assoc]
      exact mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_left HB (pow_nonneg gp.le _)).trans pβ) hK
    calc _ = τ*β+τ*(H*(((P+1:ℕ):ℝ)*C)) := by ring
         _ ≤ g^(p+1)+g^(p+1)*(((P+1:ℕ):ℝ)*C) := add_le_add pβ front
         _ = _ := by ring
  rw [same]
  apply (add_le_add (add_le_add main pβ) (le_refl ((d:ℝ)*g^(p+1)*H*C))).trans
  change (base+(d:ℝ)*C*H)*g^(p+1) ≤ g^((p:ℝ)+1-η) at final
  calc _ = (base+(d:ℝ)*C*H)*g^(p+1) := by dsimp only [base];ring
       _ ≤ _ := final

end YM.Integration.FVA1Physical.Round2.Curvature
