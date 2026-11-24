import YM.Integration.WilsonReceivedCanonicalSocketFile
import YM.Integration.WilsonReceivedDepositedOrdinaryFactor
import YM.Integration.WilsonVacuumPreResetDepositedAction
import YM.Integration.WilsonReceivedCanonicalSocketMist

/-! All ordinary Wick numerators for the authenticated canonical stock on one fixed torus digit. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedCanonicalSocketMoments
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

open WilsonReceivedCanonicalSocketWick (printed)
open WilsonOriginalMixedGaussianTable (stock)


open private flat_constant from YM.Integration.WilsonReceivedCanonicalSocketWick
open private opening from YM.Integration.WilsonVacuumPreResetDepositedAction

def moments (B:fieldDir G (coarse R i per) 1)(r:ℕ):Grade (J) r:=
  stock (J) r (flatten B) (fun s:Finset (Fin 3)=>∏j∈s,coefficient (J) badge (c) j)
    (fun s=>flash (filed R N i per F (mass d s) (signal s)))

theorem original (simple:G.Simple)(B:fieldDir G (coarse R i per) 1)(r:ℕ):
    Order.ratio (WilsonReceivedCanonicalSocketFile.release (h:=h) R d pt q N i per hi F tag x a B r)=
    moments (h:=h) R d pt q N i per F x a B r:=by
  let vacuum:=Wick (Woods G (coarse R i per)) ((K).covariance F tag) (raiseE (φ))
  have head:constantCoeff vacuum=1:=opening _ _ (flat_constant R N i per hi F)
  have nonzero:vacuum≠0:=by
    intro hz
    rw [hz,map_zero] at head
    exact zero_ne_one head
  have base:=WilsonReceivedCanonicalSocketReed.normalized (h:=h) R d pt q N i per hi F tag a simple ∅
  simp only [Finset.prod_empty,mul_one] at base
  apply WilsonReceivedDepositedOrdinaryFactor.cancel _ _ _ _ _ vacuum head
  · apply mul_left_cancel₀ nonzero
    rw [mul_one]
    exact base.symm
  · intro j
    have nq:(J).quiet≠(J).fire j:=by
      intro eqn
      have hcard:=congrArg (fun s:(J).Mode=>s.val.card) eqn
      simp [Census.fire,Census.quiet] at hcard
    simp [WilsonCapturedPrimaryWindingVerseRoster.coefficient,Poly.part_smul,Poly.part_send,nq]

end YM.Integration.WilsonReceivedCanonicalSocketMoments

