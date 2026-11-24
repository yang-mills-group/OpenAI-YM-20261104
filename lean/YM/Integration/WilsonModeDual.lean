import YM.Integration.SelectedCofactorPriceReadout

/-! The native price-attaining dual is a single finite signed mode sum,
with a field-independent budget for the original unit radii. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonModeDual
open Function Finset Marker
open scoped Classical BigOperators
variable {V : Type} [DecidableEq V] {B : Census V}

def weights (L : Poly B →L[ℂ] ℂ) (s : B.Mode) : ℂ := L (Poly.send s 1)

theorem signed (L : Poly B →L[ℂ] ℂ) (y : Poly B) : L y = ∑ s,weights L s*y.part s := by
  have eval (j : B.Mode) (v : Poly B) : Poly.get j v = v.part j := rfl
  have eqn : y = ∑ s, y.part s • Poly.send s 1 := by
    apply Marker.Poly.ext
    intro j
    change Poly.get j y = Poly.get j (∑ s : B.Mode, y.part s • Poly.send s (1:ℂ))
    rw [map_sum]
    simp only [eval]
    simp [mul_ite]
  calc L y = L (∑ s, y.part s • Poly.send s 1) := congrArg L eqn
       _ = _ := by simp only [map_sum,map_smul,smul_eq_mul,weights]; apply Finset.sum_congr rfl; exact fun s _ => mul_comm ..

theorem price {w : V → ℝ} (hw : ∀ i, 0 ≤ w i) (hu : ∀ i,w i ≤ 1) (L : Poly B →L[ℂ] ℂ)
    (hL : ∀ y, ‖L y‖ ≤ Poly.price w y) : (∑ s, ‖weights L s‖) ≤ (Fintype.card B.Mode : ℝ) := by
  calc _ ≤ ∑ _ : B.Mode, (1:ℝ) := Finset.sum_le_sum fun s _ => by
         have h := hL (Poly.send s 1)
         rw [Poly.solo,norm_one,mul_one] at h
         exact h.trans (Finset.prod_le_one (fun i _ => hw i) (fun i _ => hu i))
       _ = _ := by simp

end YM.Integration.WilsonModeDual
