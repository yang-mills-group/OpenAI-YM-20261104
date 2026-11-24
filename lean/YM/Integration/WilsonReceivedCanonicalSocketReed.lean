import YM.Integration.WilsonReceivedCanonicalSocketWick
import YM.Integration.WilsonReceivedCanonicalSocketLevels
import YM.Integration.WilsonReceivedDepositedVerseCensus
import YM.Integration.WilsonOriginalFoldedMarkedRightColumn

/-! All ordinary Wick numerators for the authenticated canonical stock on one fixed torus digit. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedCanonicalSocketReed
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
variable {G:Gauge}(R:Run G)(d:Fin 3→ℕ){h:Fin 3→ℕ}(pt:Fin 3→Chamber)
  (q:(j:Fin 3)→Choice R d j)(N i per:ℕ)(hi:i<N)
  (F:Forest (step R i per).ratio)(tag:(step R i per).Choices)
  (x:Affinity.Wallet disks)(a:Fin 3→Lattice.Cover)
local notation "J" => Stock.census (Fin 3)
local notation "K" => model R N i per hi
local notation "S" => step R i per
local notation "f" => fine R i per
local notation "A" => saddle R N i per F
local notation "ρ" => fderiv ℝ ((K).b F) 0
local notation "κ" => (fun j=>contact (h j))
local notation "φ" => relative R N i per hi F (covered R N i per)
local notation "badge" => (fun j:Fin 3=>(J).fire j)
local notation "c" => (fun j:Fin 3=>probe j x)

open WilsonVacuumPreResetStationaryChange WilsonOriginalFoldedMarkedRightColumn WilsonCoeffUV.Mer
open WilsonReceivedCanonicalVerseRegister WilsonReceivedCanonicalVerseBasis

local notation "roll" => start R d κ pt q a
local notation "ink" => WilsonReceivedCanonicalSocketWick.inlet (h:=h) R d pt q N i per hi F a
local notation "signal" t:max => (WilsonReceivedDepositedVerseCensus.ordinary (roll) (present h) t).1 (f)

theorem submitted (s:Finset (Fin 3)):
    ∏j∈s,(ink) j=before R N i per hi F (signal s):=by
  change (∏j∈s,SignedMeasuredSourceSeries.probe (S) F (A) (ρ) (readO (present h) ((roll) {j}) (f)))=
    SignedMeasuredSourceSeries.probe (S) F (A) (ρ) (readO (present h) (levelsO (roll) s) (f))
  rw [WilsonReceivedCanonicalSocketLevels.canonical R d κ pt q a (present h) (f) s,map_prod]

theorem normalized (simple:G.Simple)(s:Finset (Fin 3)):
    Wick (Woods G (coarse R i per)) ((K).covariance F tag) (raiseE (φ)*∏j∈s,(ink) j)=
      Wick (Woods G (coarse R i per)) ((K).covariance F tag) (raiseE (φ))*
        flash (filed R N i per F (mass d s) (signal s)):=by
  rw [submitted (h:=h) R d pt q N i per hi F a s]
  have funded:Eu d (roll):=IndependentSourcePathFamily.legal _ a (fun j _=>grade R d κ pt j (q j))
  have material:Auth (mass d s) (WilsonReceivedDepositedVerseCensus.ordinary (roll) (present h) s):=
    (placedO (roll) funded s).tuft (touch (present h) s)
  exact WilsonOriginalFoldedMarkedRightColumn.normalized R N i per hi F tag simple _ _
    (material.span (f)) (material.pale (f))

end YM.Integration.WilsonReceivedCanonicalSocketReed
end
