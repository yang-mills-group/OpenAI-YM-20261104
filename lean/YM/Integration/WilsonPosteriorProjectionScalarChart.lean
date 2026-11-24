import YM.Integration.FVA1Physical.Round2.FormalFieldTruncation

/-! The actual scalar clock of the Wilson row equals evaluation of its
finite coefficient polynomial. No history approximation enters this identity. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPosteriorProjectionScalarChart
open Finset MSbar MSbar.Whisk MSbar.Bakery MSbar.Bakery.Film MSbar.Cacao MSbar.Rolling MSbar.CrossH Push.Uniform
open FVA1Physical.Round2.Curvature
open scoped Classical BigOperators

theorem read {σ:Type} (p:ℕ) (T:PowerSeries (Pot σ)) (g:ℝ) (z:View σ) :
    clue (renderedPolynomial T p g) z = taste p (MSbar.Bakery.Portal.picture z T) g := by
  unfold clue renderedPolynomial taste MSbar.Bakery.Portal.picture
  rw [map_sum]
  apply sum_congr rfl
  intro i _
  simp [MvPolynomial.smul_eq_C_mul]

end YM.Integration.WilsonPosteriorProjectionScalarChart
end
