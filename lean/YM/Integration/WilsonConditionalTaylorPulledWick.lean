import YM.Integration.WilsonConditionalTaylorWick
import YM.MSbar.Rolling.Natural

/-! Evaluation after the original polynomial stationary-coordinate map
preserves the normalized real Gaussian column at its actual affine mean. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorPulledWick

open PowerSeries Matrix MSbar MSbar.Cacao MSbar.Rolling MSbar.Bakery MSbar.Bakery.Portal
open WilsonMovingNormalizedBank
open scoped Matrix Classical

variable {I J V : Type} [Fintype I] [Fintype J] [Fintype V] [DecidableEq I] [DecidableEq J] [DecidableEq V]
    (B : Matrix J I ℝ) (D : Matrix J V ℝ) (Z : View V) (Q : Matrix I I ℝ)

omit [DecidableEq J] [DecidableEq V] in
theorem pulled (T : PowerSeries (Pot J)) :
    view Z (PowerSeries.map (rail D).toRingHom T)=view (D*ᵥZ) T := by
  ext1 i
  simp only [view,coeff_map]
  exact congrFun (Rolling.clearL D Z) (coeff i T)

omit [DecidableEq V] in
theorem finite (sym : Q.IsSymm) (pos : Q.PosDef) (f T : PowerSeries (Pot J)) (kind : Kind f)
    (p : ℕ) (g : ℝ) :
    taste p (view Z (PowerSeries.map (rail D).toRingHom (growP f T (B*Q*B.transpose) (p+1)))) g =
      taste p (WilsonConditionalTaylorWick.quotient B (D*ᵥZ) Q f T) g := by
  rw [pulled]
  exact WilsonConditionalTaylorWick.finite B (D*ᵥZ) Q sym pos f T kind p g

end YM.Integration.WilsonConditionalTaylorPulledWick
end

