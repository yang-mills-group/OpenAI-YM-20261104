import YM.Integration.WilsonReceivedDepositedOrbitalSpentBoard
import YM.Integration.WilsonNeutralTwoPrintPathBoardAxis
import YM.Integration.WilsonNeutralTwoPrintPathBoardAngular

/-! A single common volume for each marked part of the original physical
board after its genuine nonlinear reset, at the physically conveyed held
direction and the signed finite tensor sum of its independent sheets. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
namespace YM.Integration.WilsonNeutralTwoPrintPathBoardPortrait
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

open WilsonReceivedCanonicalSocketSeed
open WilsonNeutralTwoPrintPathInheritedBlocks (gathered)
open WilsonReceivedCompactVerseEntrance (CoverBill submit)
open WilsonReceivedDepositedOrbitalPages (offered)
open WilsonCoeffUV.Embroider.Canvas WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Bank.Mosaic.Near

open WilsonOriginalThreeCopiedCharts WilsonOriginalMixedBlockRows WilsonOlderFreshGraphSlate
open WilsonOriginalCensusCopySlate WilsonReceivedDepositedOrbitalFixedMoments
open WilsonVacuumPreResetDepositedLetters WilsonCoeffUV.Bank.Mosaic

open WilsonOriginalCensusDeckMean (mean)
open WilsonNeutralTwoPrintPathBoxMean (plotted)
open WilsonNeutralTwoPrintPathPageRead (lower)
open WilsonNeutralTwoPrintPathBoardSeats (homes)
open WilsonNeutralTwoPrintPathFineFiber (seats)
open WilsonNeutralTwoPrintPathCalendar (spent)
open WilsonNeutralTwoPrintPathJet (diagonal)
open WilsonOriginalRawQReversion (coordinates)
open WilsonCoeffUV.Wheel.Flooring
variable {G:Gauge}{n:ℕ}{n':Side}{I:Type}[Fintype I][DecidableEq I]
  {P:Passport n' (Fin n)}(B:I→Binder P (Stock.census (Fin n))){D k:Fin n→ℕ}
  (old:Outerm G D)(q:ℕ)(c:I→Fin n)(y:Fin n→Lattice.Cover)(t:Case D)(R:Run G)(N j per:ℕ)
local notation "patch" => loose (levels R) j
local notation "ranks" => fun l:I=>mass k ((B l).mode.val)
local notation "origin" => fun l:I=>(B l).center
local notation "catalog" => WilsonReceivedDepositedOrbitalFixedMoments.program (k:=k) old q
  (fun l:I=>(B l).mode.val) c (fun _:I=>y) (fun _:I=>t)
local notation "paper" => @WilsonReceivedDepositedOrbitalFixedMoments.reading I

theorem original {grid:Side}(baseGeometry:n'.val=grid.val*(patch).L.val)
    (proj:grid.val∣(coarse R j per).val)(h:n'.val∣(fine R j per).val)
    (S:Finset I)(o:S)(root:Site (coarse R j per))(site:(S.erase o.val)→Site (coarse R j per))
    (base:Fin (Pages grid (coarse R j per)))
    (atRoot:(page proj (homes (patch) baseGeometry (origin) o.val) base).val=root)
    (others:∀i:S.erase o.val,splitter proj (site i)=homes (patch) baseGeometry (origin) i.val)
    (d:ℕ)(A:Stationary.Link G grid):
    let X:=coarse R j per
    let digit:=fun l:I=>(Ratio.mk (patch).L baseGeometry:Ratio grid n').residue ((origin) l)
    let high:=fun (sheets:S→Fin (Pages n' (fine R j per)))=>
      let seated:=seats (patch) (step R j per).sizes proj h S (origin) sheets o
      let res:=spent R (ranks) N j q X (catalog) seated digit S
      Complex.ofReal (diagonal (mass (ranks) S+d) (fun r z=>touch (paper) S (res d r z))
        ((coordinates G X) (AllOrder.Ker.convey (coverWin proj) A)))
    let T:=fun r=>mean proj (plotted proj S o.val root site
      (fun place=>spent R (ranks) N j q X (catalog) place digit S d r)
      (Complex.ofRealCLM.comp (touch (paper) S))
      (fun z=>∏i:Fin r,((coordinates G grid) A (z i):ℂ)))
    (Pages grid X:ℂ)⁻¹*∑sheets,high sheets=∑r∈range (mass (ranks) S+d+1),T r:=by
  intro X digit high T
  have received:=WilsonNeutralTwoPrintPathBoardAngular.original (patch) baseGeometry (step R j per).sizes
    proj h S o (origin) root site base atRoot others (mass (ranks) S+d)
    (fun place r=>spent R (ranks) N j q X (catalog) place digit S d r)
    (touch (paper) S) ((coordinates G grid) A)
  dsimp only [high,T]
  rw [WilsonNeutralTwoPrintPathBoardAxis.original]
  exact received

end YM.Integration.WilsonNeutralTwoPrintPathBoardPortrait
end
