import YM.Integration.WilsonMovingGaussianCoordinates
import YM.FormalBulk08.Jets.Knit

/-! The finite addressed Taylor tensor used by the Wilson lamp and the formal
cover polynomial use the same factorial, including repeated physical links. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMovingTaylorConvention
open Function PowerSeries FormalBulk08 FormalBulk08.Jets FormalBulk08.Series
open scoped BigOperators Classical ContDiff PowerSeries
variable {I J : Type} [Fintype I] [Fintype J]

/-- Full ordered tensor, including repeated directions. -/
def tensor (f : Rays I → ℝ) (n : ℕ) : MvPolynomial I ℝ :=
  ∑ a : Fin n → I, MvPolynomial.C (Tensor.coeff f n 0 (dotI ∘ a)) *
    ∏ j, MvPolynomial.X (a j)

theorem coefficient (f : Rays I → ℝ) (n : ℕ) :
    tensor f n = coeff n (paste f) := by
  rw [tensor, paste_coeff, laden, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [Tensor.coeff, smul_apply, smul_eq_mul,
    map_mul, Algebra.smul_def, mul_assoc]
  rfl

/-- A genuine finite placement. The physical site map need not be injective:
when two addressed slots coincide, the corresponding variables are added at
the same link under the original polynomial rename. -/
theorem placed (s : I → J) (f : Rays I → ℝ) (smooth : ContDiffAt ℝ ∞ f 0) :
    PowerSeries.map (MvPolynomial.rename s).toRingHom (paste f) =
      paste (fun x : Rays J => f (x ∘ s)) := by
  have sub : ContDiffAt ℝ ∞ (fun x : Rays J => x ∘ s) 0 := by
    change ContDiffAt ℝ ∞ (fun (x : Rays J) (i : I) => x (s i)) 0
    fun_prop
  change _ = paste (f ∘ (fun x : Rays J => x ∘ s))
  rw [paste_steps f _ smooth sub rfl, fit_translate s]

theorem occupied (s : I → J) (f : Rays I → ℝ) (smooth : ContDiffAt ℝ ∞ f 0)
    (n : ℕ) : MvPolynomial.rename s (tensor f n) =
      coeff n (paste (fun x : Rays J => f (x ∘ s))) := by
  rw [coefficient, ← placed s f smooth]
  rfl

end YM.Integration.WilsonMovingTaylorConvention
end

