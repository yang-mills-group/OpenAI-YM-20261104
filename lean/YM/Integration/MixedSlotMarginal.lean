import YM.Integration.NativeMixedSlotProduct
import Mathlib.Algebra.BigOperators.Fin

/-! Sum the exact separated-product estimate over every unfixed field slot.
Coupling slots remain fixed at one and may occur in any explicit order. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.MixedSlotMarginal
open Function
open Comparison.RG02.Assembly
open scoped BigOperators Classical

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type} [Fintype ι]

/-- The same field-coordinate marginal pays a separated coupling multiplier. -/
theorem product_marginal {h : ℝ → ℝ} {f : E → ℝ}
    (hh : AnalyticAt ℝ h 0) (hf : AnalyticAt ℝ f 0)
    (c d : ℕ) (v : ι → E) (j : Fin (d + 1)) (i0 : ι)
    (σ : Equiv.Perm (Fin (c + (d + 1)))) {A : ℝ}
    (hA : (∑ q : Fin d → ι,
      ‖(((d + 1).factorial : ℝ)⁻¹) *
        iteratedFDeriv ℝ (d + 1) f 0
          (fun t => v (Fin.insertNth (α := fun _ => ι) j i0 q t))‖) ≤ A) :
    (∑ q : Fin d → ι,
      ‖(((c + (d + 1)).factorial : ℝ)⁻¹) *
        iteratedFDeriv ℝ (c + (d + 1))
          (NativeMixedSlotProduct.product h f) 0
          (NativeMixedSlotProduct.slots c
            (fun t => v (Fin.insertNth (α := fun _ => ι) j i0 q t)) ∘ σ)‖) ≤
      |jet h c 1| * A := by
  calc
    _ ≤ ∑ q : Fin d → ι, |jet h c 1| *
        ‖(((d + 1).factorial : ℝ)⁻¹) *
          iteratedFDeriv ℝ (d + 1) f 0
            (fun t => v (Fin.insertNth (α := fun _ => ι) j i0 q t))‖ := by
      apply Finset.sum_le_sum
      intro q _hq
      simpa only [Real.norm_eq_abs] using
        NativeMixedSlotProduct.normalized_bound hh hf c (d + 1)
          (fun t => v (Fin.insertNth (α := fun _ => ι) j i0 q t)) σ
    _ = |jet h c 1| * (∑ q : Fin d → ι,
        ‖(((d + 1).factorial : ℝ)⁻¹) *
          iteratedFDeriv ℝ (d + 1) f 0
            (fun t => v (Fin.insertNth (α := fun _ => ι) j i0 q t))‖) :=
      (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hA (abs_nonneg _)

end YM.Integration.MixedSlotMarginal
end
