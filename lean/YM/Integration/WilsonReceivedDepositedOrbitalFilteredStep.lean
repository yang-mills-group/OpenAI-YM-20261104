import YM.Integration.WilsonReceivedDepositedOrbitalFilteredLog
import YM.Integration.WilsonReceivedDepositedSocketRows

/-! The genuine conditional, its complete vacuum and its measured kinetic clock retain finite grades of the old ordinary rows. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedDepositedOrbitalFilteredStep
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

open WilsonReceivedDepositedOrbitalFilteredLog
open WilsonCoeffUV.Blue WilsonVacuumPreResetMeasuredCoin WilsonVacuumPreResetDatedDeposit
open private flat_constant from YM.Integration.WilsonReceivedCanonicalSocketWick
open private opening from YM.Integration.WilsonVacuumPreResetDepositedAction
open WilsonReceivedCanonicalSocketMist WilsonReceivedDepositedVerseCensus
open WilsonCoeffUV.Wheel.Flooring WilsonCoeffUV.Wheel.Address
local notation "γ" => ratioHigh (levels R) R.metals.O N i
local notation "word" M:max w:max v:max => (WilsonReceivedDepositedVerseCensus.ordinary (M) (w) (v)).1 (f)
local notation "seed" M:max w:max v:max => flash (filed R N i per F (mass k (v)) (word (M) (w) (v)))
local notation "clock" M:max v:max => mist (step R i per) F (upper R N i) (prediction R N i per) (ratio R)
  (covered R N i per) (M) (γ) k (v)

theorem normalized (simple:G.Simple)(tag:(step R i per).Choices)
    (M:family G h)(paid:Eu k M)(hush:M ∅=0)(w:Case h)(s:Finset I):
    Wick (Woods G (c)) ((K).covariance F tag) (raiseE (φ)*before R N i per hi F (word M w s))=
      Wick (Woods G (c)) ((K).covariance F tag) (raiseE (φ))*(seed M w s):=by
  rw [WilsonReceivedDepositedSocketRows.ordinary R N i per hi F M paid hush w s]
  exact WilsonReceivedDepositedSocketRows.normalized R N i per hi F simple tag M paid hush w s

theorem original (simple:G.Simple)(tag:(step R i per).Choices)(d:ℕ)
    (M M':family G h)(paid:Eu k M)(nextPaid:Eu k M')(hush:M ∅=0)(nextHush:M' ∅=0)
    (w:Case h)(s:Finset I)
    (input:∀v⊆s,Equal d (before R N i per hi F (word M w v)) (before R N i per hi F (word M' w v))):
    Equal d (flash (pPly w s (clock M s))) (flash (pPly w s (clock M' s))):=by
  have left:=WilsonReceivedCanonicalSocketMist.deposited R N i per hi F M paid w simple
  have right:=WilsonReceivedCanonicalSocketMist.deposited R N i per hi F M' nextPaid w simple
  apply WilsonReceivedDepositedOrbitalFilteredLog.through d left right s
  intro v part
  apply WilsonReceivedDepositedOrbitalFilteredLog.kinetic
  let unmarked:=Wick (Woods G (c)) ((K).covariance F tag) (raiseE (φ))
  have nonzero:PowerSeries.constantCoeff unmarked=1:=opening _ _ (flat_constant R N i per hi F)
  apply WilsonReceivedDepositedOrbitalFilteredLog.canceled d nonzero
  have first:=normalized R N i per hi F simple tag M paid hush w v
  have second:=normalized R N i per hi F simple tag M' nextPaid nextHush w v
  rw [←first,←second]
  exact WilsonReceivedDepositedOrbitalFilteredLog.wick _ _
    ((Equal.refl (raiseE (φ)) d).mul (input v part))

end YM.Integration.WilsonReceivedDepositedOrbitalFilteredStep
end
