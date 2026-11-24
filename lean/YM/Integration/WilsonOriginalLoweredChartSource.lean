import YM.Integration.WilsonOriginalRegisteredChartInsertion
import YM.Integration.WilsonOriginalChargedSourceHead

/-! Lowering the polynomial source on its actual original chart while keeping the full two-chart Gaussian numerator and denominator. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalLoweredChartSource
open Function Finset Lattice Laurent Bloch Wilson RG Precision Exterior Tree Matrix PowerSeries
open PhysicalNext.Repeat.Legato Comparison.RG02 FreeResolvent WilsonCoeffUV WilsonCoeffUV.Bank
open WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open WilsonCoeffUV.Winding WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider WilsonCoeffUV.Bank.Mosaic
open WilsonVacuumPreResetStationaryChange WilsonVacuumPreResetDepositedRay WilsonVacuumPreResetDepositedGeometric
open WilsonVacuumPreResetOriginalOutput (covered)
open WilsonOriginalRelativeFoldedQuiet (relative)
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
attribute [local instance] Gauge.frobInner
variable {G:Gauge}(R:Run G)(N i p:ℕ)(hi:i<N)(F:Forest (step R i p).ratio)(tag:(step R i p).Choices)
local notation "P" => covered R N i p
local notation "K" => model R N i p hi
local notation "C₁" => Woods G (coarse R i p)

open OriginalMarkedSourceComet IndependentSourcePathFamily
variable {V:Type}[DecidableEq V]{D:V→ℕ}(o:V)(a:Seed G (D o))(x:Case D)(y:Cover)

abbrev slot (h:ℕ) : Seed G (D o) := {a with head:=a.rank-h}

theorem shift (h:ℕ)(ha:a.head=a.rank)(fit:h≤a.rank) :
    SignedOpeningSourceCurrent.independent K F (saddle R N i p F) o a x y =
    PowerSeries.X^h*SignedOpeningSourceCurrent.independent K F (saddle R N i p F) o (slot o a h) x y:=by
  let ρ:=fderiv ℝ ((K).b F) 0
  let reader:=SignedMeasuredSourceSeries.probe (step R i p) F (saddle R N i p F) ρ
  have core:reader (PowerSeries.X:Ink (Woods G (fine R i p)))=PowerSeries.X:=by
    simp [reader,SignedMeasuredSourceSeries.probe,loom,retool,reroll_X]
  let T:=colour a.path a.color a.weight a.quadrant
  change reader (readO x (source D o T a.knob a.point a.head y) (fine R i p)) =
    PowerSeries.X^h * reader (readO x (source D o T a.knob a.point (a.rank-h) y) (fine R i p))
  rw [ha,WilsonOriginalChargedSourceHead.radial o T a.knob a.point y fit _ x,map_mul,map_pow,core]

theorem coefficient (h:ℕ)(ha:a.head=a.rank)(fit:h≤a.rank)(j:ℕ) :
    PowerSeries.coeff (j+h) (SignedOpeningSourceCurrent.independent K F (saddle R N i p F) o a x y) =
    PowerSeries.coeff j (SignedOpeningSourceCurrent.independent K F (saddle R N i p F) o (slot o a h) x y):=by
  rw [shift R N i p hi F o a x y h ha fit,coeff_X_pow_mul']
  simp

end YM.Integration.WilsonOriginalLoweredChartSource
