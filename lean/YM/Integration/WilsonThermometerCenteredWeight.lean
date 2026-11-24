import YM.Integration.WilsonThermometerCenteredCompensation

/-! Restore the signed inverse table together with its measured faces.
The two complementary modes partition the three original source names. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerCenteredWeight
open Primitives.GCC.Anchor
open Finset Marker QuadraticLocal WilsonThermometerCenteredAlgebra WilsonFiniteOrdinaryInverse
open scoped BigOperators Classical
local notation "J" => Stock.census (Fin 3)

private def flip : (J).Mode ≃ (J).Mode where
  toFun := complement
  invFun := complement
  left_inv s := by apply Subtype.ext; ext i; simp [complement]
  right_inv s := by apply Subtype.ext; ext i; simp [complement]

theorem original (Q : Poly J) (w : Fin 3 → ℝ) (positive : ∀ v, 0<w v)
    {g : ℝ} (gp : 0<g) (small : g≤1) (loss : ℕ) (fullPrice : g^loss≤Poly.toll w full)
    (inverse : Poly.price (fun v=>g*w v) (inverseMass Q) ≤ fee J) :
    g^(3+loss)*(∑ s : (J).Mode, ‖weight Q s‖/Poly.toll w s) ≤ fee J := by
  rw [mul_sum]
  calc
    _ ≤ ∑ s : (J).Mode,Poly.toll (fun v=>g*w v) (complement s)*‖weight Q s‖ := by
      apply sum_le_sum
      intro s _
      have wp : 0 < Poly.toll w s := prod_pos fun v _ => positive v
      have partition : Poly.toll w (complement s)*Poly.toll w s=Poly.toll w full := by
        change (∏ v∈univ \ s.val,w v)*(∏ v∈s.val,w v)=∏ v:Fin 3,w v
        exact Finset.prod_sdiff (f:=w) (Finset.subset_univ s.val)
      have cards : (complement s).val.card ≤ 3 := by simpa using Finset.card_le_univ (complement s).val
      have joint : g^(3+loss) ≤ Poly.toll (fun v=>g*w v) (complement s)*Poly.toll w s := by
        rw [scaled,mul_assoc,partition,pow_add]
        exact mul_le_mul (pow_le_pow_of_le_one gp.le small cards) fullPrice
          (pow_nonneg gp.le _) (pow_nonneg gp.le _)
      calc
        _ = (g^(3+loss)/Poly.toll w s)*‖weight Q s‖ := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right ((div_le_iff₀ wp).2 joint) (norm_nonneg _)
    _ = Poly.price (fun v=>g*w v) (inverseMass Q) := Equiv.sum_comp flip
      (fun s : (J).Mode => Poly.toll (fun v=>g*w v) s*‖(inverseMass Q).part s‖)
    _ ≤ fee J := inverse

end YM.Integration.WilsonThermometerCenteredWeight
