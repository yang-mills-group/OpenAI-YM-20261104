import YM.Integration.WilsonReceivedDepositedOrbitalCofinalClock
import YM.Integration.WilsonThermometerOriginalPupilDegree

/-! A real copy lift and the single volume normalization commute with the measured kinetic reading. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedDepositedOrbitalCofinalLift
open Lattice RG Marker Multi FVA1Physical.Wilson Exterior QuadraticLocal.Earn QuadraticLocal.Sunrise FVA1Physical.TwoReset
open Finset Comparison.RG02 Comparison.RG02.Valence Comparison.RG02.Adjacent Comparison.RG02.Moving
open Moving.Path
open scoped Topology BigOperators ContDiff
variable {E F:Type*}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]

def pulled (c:ℂ)(L:E→L[ℝ]F)(U:Display F):Display E:=fun j y=>c*U j (L y)

theorem priced (c:ℂ)(L:E→L[ℝ]F)(r:ℕ)(height:ℕ→ℕ)(U:Display F)(fund:Charge r (fun j=>(height j:ℤ)) U):
    Charge r (fun j=>(height j:ℤ)) (pulled c L U):=by
  intro j inside
  change Level ((height j):ℤ) (fun z:E=>c*U j (L z))
  have h:=SignCovariance.affine_degree (0:F) L (fund j inside)
  simpa only [pulled,zero_add] using h.factor c

theorem original (c:ℂ)(L:E→L[ℝ]F)(U:Display F)(T:UnitCost)(weight:ℤ)(r d:ℕ)(height:ℕ→ℤ)
    (fund:Charge r height U)(x:E):
    born (pulled c L U) T weight r d x=c*born U T weight r d (L x):=by
  have same (a:ℝ):ages (pulled c L U) weight r a (T.rating a) x=c*ages U weight r a (T.rating a) (L x):=by
    unfold ages cover pulled
    simp only [map_smul,mul_sum]
    apply sum_congr rfl
    intro j _
    ring
  have smooth:ContDiffAt ℝ ω (fun a=>ages U weight r a (T.rating a) (L x)) 0:=by
    simp_rw [quoted weight r fund]
    exact ContDiffAt.sum (fun j _=>ContDiffAt.sum (fun k _=>(monetized T weight j k).mul contDiffAt_const))
  unfold born
  rw [funext same,Shift.mscale c smooth]

end YM.Integration.WilsonReceivedDepositedOrbitalCofinalLift
end
