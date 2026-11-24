import YM.Integration.WilsonOriginalFoldedChartPayload

/-! The same registered transported-curvature source on the two physical Gaussian charts. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalRegisteredChartInsertion
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

/-- The true lifted source on the original affine slice, before its nonlinear re-expression. -/
def input : Ink (Active G F⊕C₁) :=
  loom (slice R N i p F) (readO x (source D o (colour a.path a.color a.weight a.quadrant)
    a.knob a.point a.head y) (fine R i p))

theorem represented : retool (shift R N i p hi F) (input R N i p F o a x y) =
    SignedOpeningSourceCurrent.independent K F (saddle R N i p F) o a x y := rfl

theorem original (simple:G.Simple) :
    let φ:=WilsonOriginalRelativeFoldedQuiet.relative R N i p hi F P
    let ψ:=shot (step R i p) F (prediction R N i p) (ratio R) P
    let Q:=(K).covariance F tag
    Wick (C₁) Q (raiseE ψ * input R N i p F o a x y) =
      Wick (C₁) Q (raiseE φ * SignedOpeningSourceCurrent.independent K F (saddle R N i p F) o a x y) ∧
      inside (step R i p) F (upper R N i) (prediction R N i p) (ratio R) P =
        Wick (C₁) Q (raiseE φ) :=by
  exact WilsonOriginalFoldedChartPayload.original R N i p hi F tag simple (input R N i p F o a x y)

end YM.Integration.WilsonOriginalRegisteredChartInsertion
