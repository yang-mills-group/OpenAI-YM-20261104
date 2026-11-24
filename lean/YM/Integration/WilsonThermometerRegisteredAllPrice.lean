import YM.Integration.WilsonThermometerRegisteredAllMaterial

/-! Restoration at the common measured aperture for every thermometer face. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerRegisteredAllPrice
open Function Filter Finset RG Lattice Wilson Tree Source Labels Marker QuadraticLocal QuadraticLocal.Earn
open Multi Comparison.RG02.Cumulants WilsonIndependentOrdinaryPairGrade
open scoped BigOperators Classical
local notation "J" => Stock.census (Fin 3)
def fee : ℝ := 25*(Fintype.card (Multi.parts (J)).Mode : ℝ)

theorem paid {g w value:ℝ} (p:ℕ) (s:(J).Mode) (gp:0 < g) (small:g ≤ 1)
    (roof:g^157 ≤ w) (priced:w*value ≤ WilsonThermometerRegisteredWindow.bill s g (g^(p+161)) (p+158)) :
    value ≤ fee*g^(p+1) := by
  have wp:0 < w:=(pow_pos gp _).trans_le roof
  have inv:1 ≤ g⁻¹:=one_le_inv_iff₀.mpr ⟨gp,small⟩
  have en:0 ≤ g^(p+161):=pow_nonneg gp.le _
  have eu:g^(p+161) ≤ 1:=pow_le_one₀ gp.le small
  have size:s.val.card ≤ 3:=(Finset.card_le_univ s.val).trans_eq (Fintype.card_fin 3)
  have head (b:(Multi.parts (J)).Mode) (member:b∈shards (J) s) :
      (b.val.card:ℝ)*g^(p+161)*(g⁻¹+g^(p+161))^b.val.card ≤ 24*g^(p+158):=by
    have card:= (WilsonFiniteOrdinaryTail.blocks s b member).trans size
    have cover:g⁻¹+g^(p+161) ≤ 2*g⁻¹:=by linarith only [eu,inv]
    have power:(g⁻¹+g^(p+161))^b.val.card ≤ (2*g⁻¹)^3:=
      (pow_le_pow_left₀ (add_nonneg (inv_nonneg.mpr gp.le) en) cover _).trans
        (pow_le_pow_right₀ (by linarith only [inv]) card)
    have cardr:(b.val.card:ℝ) ≤ 3:=by exact_mod_cast card
    calc
      _ ≤ 3*g^(p+161)*(2*g⁻¹)^3:=mul_le_mul (mul_le_mul_of_nonneg_right cardr en) power
        (pow_nonneg (add_nonneg (inv_nonneg.mpr gp.le) en) _) (by positivity)
      _ = _:=by rw [show p+161=p+158+3 from by omega,pow_add];field_simp;ring
  have shipped:w*value ≤ fee*g^(p+158):=priced.trans (by
    unfold WilsonThermometerRegisteredWindow.bill
    calc
      _ ≤ (∑ _b∈shards (J) s,24*g^(p+158))+g^(p+158)*(shards (J) s).card :=
        add_le_add (Finset.sum_le_sum head) le_rfl
      _ = (25*(shards (J) s).card)*g^(p+158):=by simp;ring
      _ ≤ _:=by unfold fee;gcongr;exact Finset.card_le_univ _)
  have finish:g^157*(fee*g^(p+1))=fee*g^(p+158):=by
    rw [show p+158=157+(p+1) from by omega,pow_add];ring
  apply (le_of_mul_le_mul_left · wp)
  calc
    w*value ≤ fee*g^(p+158):=shipped
    _ = g^157*(fee*g^(p+1)):=finish.symm
    _ ≤ w*(fee*g^(p+1)):=mul_le_mul_of_nonneg_right roof (mul_nonneg (by unfold fee;positivity) (pow_nonneg gp.le _))

end YM.Integration.WilsonThermometerRegisteredAllPrice
