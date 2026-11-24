import YM.Integration.WilsonPositionScaleLawGuardCancellation
/-! A fixed noncommuting scale calculation with its finite polynomial overflow. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawGuardSheet
open PowerSeries MS.Book.Program
open WilsonPositionScaleLawGuardPoly (value mass)
open WilsonPositionScaleLawGuardSubstitute (system)
open WilsonPositionScaleLawGuardCancellation (fringe)
open scoped Polynomial Classical
variable (R:Type*)[NormedRing R][NormedAlgebra ℂ R]
structure Book where
  scalar : PowerSeries ℂ
  correction : PowerSeries R
  turned : PowerSeries R
  homogeneous : PowerSeries R
  position : PowerSeries R
variable {R}
def Valid (p:Book R):Prop:=Rooted p.scalar ∧ p.turned*p.homogeneous=p.position*system p.scalar p.correction
def total (p:Book R)(q:ℕ):ℝ:=mass (fringe q p.scalar p.correction p.turned p.homogeneous p.position)
abbrev atValue (q:ℕ)(a:PowerSeries R)(z:ℂ):=value (trunc (q+1) a) z
def carries (p:Book R)(D:R):Prop:=∀q z,atValue q p.correction z*D=D*atValue q p.turned z
def Quote (p:Book R)(D:R):Prop:=∀q (z:ℂ),‖z‖≤1→
  ‖D*(atValue q p.position z*atValue q p.correction ((trunc (q+1) p.scalar).eval z))-
   atValue q p.correction z*D*atValue q p.homogeneous z‖≤‖D‖*(‖z‖^(q+1)*total p q)
theorem booked (p:Book R)(v:Valid p)(D:R)(h:carries p D):Quote p D:=by
  intro q z hz
  have fee:=WilsonPositionScaleLawGuardCancellation.original q p.scalar v.1
    p.correction p.turned p.homogeneous p.position v.2 hz
  rw [h q z,mul_assoc,←mul_sub]
  exact (norm_mul_le D _).trans (mul_le_mul_of_nonneg_left fee (norm_nonneg D))
end YM.Integration.WilsonPositionScaleLawGuardSheet
