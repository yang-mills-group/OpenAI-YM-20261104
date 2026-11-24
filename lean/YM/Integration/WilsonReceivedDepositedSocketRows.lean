import YM.Integration.WilsonReceivedCanonicalSocketWick
import YM.Integration.WilsonReceivedCanonicalSocketMoments
import YM.Integration.SignedJointSourceMoments
import YM.Integration.WilsonReceivedDepositedVerseCensus
import YM.Integration.WilsonOriginalFoldedMarkedRightColumn

/-! All ordinary Wick numerators for the authenticated canonical stock on one fixed torus digit. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedDepositedSocketRows
open Function Filter Finset Lattice Wilson Laurent RG Source Labels Marker Multi QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Sunrise
open Comparison.RG02 Comparison.RG02.Cumulants Next.SectorChange AllOrder AllOrder.Floe
open PhysicalNext.Repeat.Legato Further.PhysicalPeriodLimitF933 Macrame Shingle
open FVA1Physical.TwoReset WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Embroider WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Soil
open WilsonVacuumPreResetStationaryChange WilsonVacuumPreResetDepositedGeometric
open WilsonOriginalStarSceneWords WilsonThermometerDeclaredSeeds WilsonOriginalThermometerPalette
open WilsonReceivedCanonicalSocketRows WilsonReceivedCanonicalSocketFields WilsonReceivedCanonicalSocketSeed
open Pressure Push Push.AbsoluteSums Precision Tree Exterior Bloch PowerSeries
open PhysicalForestMarkedRay FVA1Physical.TwoReset
open scoped ContDiff Topology Classical BigOperators Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
open WilsonLimitConstruction Work.F08 FullQLocal FullQLocal.RenderedStep
open WilsonVacuumPreResetDepositedIntegrand WilsonOriginalOccupiedForestIntegral WilsonOriginalMeasuredOccupiedForest
open WilsonVacuumPreResetOriginalOutput (covered)
open WilsonOriginalRelativeFoldedQuiet (relative)
open WilsonOriginalEarnedUnaryDriver (driver)
open WilsonVacuumPreResetDatedDeposit (Issued)
open WilsonOriginalThreePurchasedRays (prescribed)

open LocalComparison Comparison.RG02.Cumulants Comparison.RG02.Assembly Order AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open PertExtension Series WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank
open WilsonReceivedCanonicalSocketChannels
open WilsonOriginalEarnedUnaryDriver (driver)
open WilsonCoeffUV.Winding WilsonCoeffUV.Power Next.Rank
open FreeResolvent
open WilsonOriginalChargedForestQ WilsonVacuumPreResetFiniteRegister
open WilsonCapturedPrimaryWindingVerseRoster (coefficient)
open WilsonOriginalFoldedMarkedRightColumn WilsonCoeffUV.Mer
open WilsonCoeffUV.Wheel.Mark
open private equation from YM.Integration.SignedJointSourceMoments
variable {G:Gauge}(R:Run G)(N i per:ℕ)(hi:i<N)(F:Forest (step R i per).ratio)
  {I:Type} [DecidableEq I] {h k:I→ℕ}

local notation "K" => model R N i per hi
local notation "f" => fine R i per
local notation "c" => coarse R i per
local notation "φ" => relative R N i per hi F (covered R N i per)

def entered (M:family G h)(A:Case h)(j:Finset I):Ink (Active G F ⊕ Woods G (c)):=
  SignedMeasuredSourceSeries.probe (step R i per) F (saddle R N i per F) (fderiv ℝ ((K).b F) 0)
    (readO A (M j) (f))

theorem ordinary (M:family G h)(paid:Eu k M)(hush:M ∅=0)(A:Case h)(j:Finset I):
    before R N i per hi F ((WilsonReceivedDepositedVerseCensus.ordinary M A j).1 (f))=
      SignedJointSourceMoments.products (entered R N i per hi F M A) j:=by
  let L:=SignedMeasuredSourceSeries.probe (step R i per) F (saddle R N i per F)
    (fderiv ℝ ((K).b F) 0)
  have real:=SignedJointSourceMoments.transported (fun _:I=>0) 1 L (levels_exp M paid hush A (f))
  have law:Equation (fun t=>L (feeble (levelsO M) A (f) t)) (fun t=>L (feeble M A (f) t)):=by
    change Equation (fun t=>1^SignedJointSourceMoments.clearing (fun _:I=>0) t * L (feeble (levelsO M) A (f) t))
      (fun t=>1^SignedJointSourceMoments.clearing (fun _:I=>0) t * L (feeble M A (f) t)) at real
    simpa only [one_pow,one_mul] using real
  have e:=Equation.prod_u _ _ _ law (equation _ law.2.1)
  exact congrFun e j

theorem normalized (simple:G.Simple)(tag:(step R i per).Choices)(M:family G h)(paid:Eu k M)
    (hush:M ∅=0)(A:Case h)(j:Finset I):
    Wick (Woods G (c)) ((K).covariance F tag)
      (raiseE (φ)*SignedJointSourceMoments.products (entered R N i per hi F M A) j)=
    Wick (Woods G (c)) ((K).covariance F tag) (raiseE (φ))*
      flash (filed R N i per F (mass k j) ((WilsonReceivedDepositedVerseCensus.ordinary M A j).1 (f))):=by
  rw [←ordinary R N i per hi F M paid hush A j]
  have material:Auth (mass k j) (WilsonReceivedDepositedVerseCensus.ordinary M A j):=
    (placedO M paid j).tuft (touch A j)
  exact WilsonOriginalFoldedMarkedRightColumn.normalized R N i per hi F tag simple _ _
    (material.span (f)) (material.pale (f))

end YM.Integration.WilsonReceivedDepositedSocketRows
end

