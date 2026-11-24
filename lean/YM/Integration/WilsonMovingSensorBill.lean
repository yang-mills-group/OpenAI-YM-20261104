import YM.WilsonCoeffUV.Reclosure.CurlTorus
import YM.WilsonCoeffUV.Thermo.Distance

/-! The finite winding error tested on the complete independently occupied
field slots. The estimate retains the dimension of the actual sensor torus. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMovingSensorBill
open Lattice RG Wilson Precision Laurent Bloch WilsonCoeffUV WilsonCoeffUV.Blue
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open scoped Classical BigOperators

private theorem height {t A d b : ℝ} {n ℓ H : ℕ} (ha : 0<A) (hd : 0<d) (hb : 0<b)
    (paid : (H:ℝ)*Real.log b + (ℓ:ℝ)*Real.log d + Real.log (2*A) ≤ (t/16)*n) :
    2*(d^ℓ)*(A*Real.exp (-(t/16)*n)) ≤ b^(-(H:ℝ)) := by
  calc
    _ = Real.exp (Real.log (2*A) + (ℓ:ℝ)*Real.log d + (-(t/16)*n)) := by
      rw [Real.exp_add, Real.exp_add, Real.exp_log (by positivity), Real.exp_nat_mul,Real.exp_log hd]
      ring
    _ ≤ Real.exp (Real.log b*(-(H:ℝ))) := by
      apply Real.exp_le_exp.mpr
      linarith only [paid]
    _ = _ := (Real.rpow_def_of_pos hb _).symm

/-- All signed polarizations of the full folded cover-minus-sensor tensor. No
spatial slots are dropped, and the finite sensor precedes the directional test. -/
theorem polarized {G : Gauge} {n : Side} {r H : ℕ} {t A b : ℝ}
    (F : post G r) (P : Ten ℝ (Co n (Hooks G)) (r+1))
    (width : 0<t) (income : 0<A) (warm : 0<b)
    (kernel : Amber (tor n) (t/2) (A*Real.exp (-(t/16)*n.val)) (lagoon F n - P))
    (paid : (H:ℝ)*Real.log b + (r+1:ℕ)*Real.log (Fintype.card (Co n (Hooks G)):ℝ) +
       Real.log (2*A) ≤ (t/16)*n.val)
    (w : stars G r n → ℝ) (unit : ∀ x, ‖w x‖ ≤ 1) :
    2*‖∑ x:stars G r n, w x*(lagoon F n x-P x)‖ ≤ b^(-(H:ℝ)) := by
  classical
  let d : ℝ := Fintype.card (Co n (Hooks G))
  let B := A*Real.exp (-(t/16)*n.val)
  have cell (x:stars G r n) : ‖w x*(lagoon F n x-P x)‖ ≤ B := by
    have h := kernel.2 x
    rw [norm_mul]
    calc
       _ ≤ 1*‖lagoon F n x-P x‖ := mul_le_mul_of_nonneg_right (unit x) (norm_nonneg _)
       _ ≤ B := by
         rw [one_mul]
         apply h.trans
         exact mul_le_of_le_one_right kernel.1
           (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith only [width]) (by positivity)))
  have sum : ‖∑ x:stars G r n, w x*(lagoon F n x-P x)‖ ≤ d^(r+1)*B := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _x:stars G r n, B := Finset.sum_le_sum (fun x _ => cell x)
      _ = d^(r+1)*B := by simp [d,stars]
  by_cases dimension : 0<d
  · have h := height (n:=n.val) (ℓ:=r+1) income dimension warm paid
    exact (mul_le_mul_of_nonneg_left sum (by norm_num : 0 ≤ (2:ℝ))).trans (by simpa [B,mul_assoc] using h)
  · have zero : d=0 := le_antisymm (le_of_not_gt dimension) (by dsimp [d]; positivity)
    rw [zero,zero_pow (Nat.succ_ne_zero r),zero_mul] at sum
    exact (mul_nonpos_of_nonneg_of_nonpos (by norm_num) sum).trans (Real.rpow_nonneg warm.le _)


end YM.Integration.WilsonMovingSensorBill
