import YM.Integration.WilsonNeutralTwoPrintPathBoardSeam
import YM.Integration.WilsonNeutralTwoPrintPathBoardCentralSeats
import YM.Integration.WilsonOriginalCensusRosterFare
import YM.Integration.WilsonOriginalCensusCentralSheet

noncomputable section
namespace YM.Integration.WilsonNeutralTwoPrintPathBoardCentral
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

open WilsonReceivedCoverGrade (Through)
open WilsonReceivedDepositedOrbitalFixedMoments (program reading)
open WilsonNeutralTwoPrintPathCalendar (spent)
open WilsonNeutralTwoPrintPathJet (diagonal)
open WilsonOriginalRawQReversion (coordinates)

variable {G:Gauge}{n:ℕ}{D k:Fin n→ℕ}{I:Type}[Fintype I][DecidableEq I]


open WilsonOriginalCensusRosterFare (whole)
open WilsonNeutralTwoPrintPathFineFiber (seats)
open WilsonNeutralTwoPrintPathBoxInk (ink)
open WilsonIndependentCollarOrbitalReception (relative)

/-- The central angular sum on arbitrary registered lifts is the actual
single-board reading of the original deposited census, including its scalar. -/
theorem original (R:Run G)(N i per:ℕ)(hi:i<N)(simple:G.Simple)(tag:(step R i per).Choices)
    (old:Outerm G D)(q:ℕ)(well:Wellness k old){σ C:ℝ}(width:0<σ)(one:1≤C)(bill:CoverBill old q σ C)
    (words:I→Finset (Fin n))(c:I→Fin n)(live:∀l,c l∈words l)(site:Fin n→Lattice.Cover)(t:Case D)
    (address:I→Site (fine R i per))(choose:∀J:Finset I,J.Nonempty→J)(S:Finset I)(place:I→Lattice.Cover)
    (located:∀l∈S,Lattice.wrap (coarse R i per) (place l)=
      (Ratio.mk (loose (levels R) i).L (step R i per).sizes:Ratio (coarse R i per) (fine R i per)).parent (address l))
    (d:ℕ)(kept:d≤q)(v:Stationary.Link G (coarse R i per)):
    let P:=loose (levels R) i
    let ff:=fine R i per
    let B:=coarse R i per
    let digit:=fun l:I=>(Ratio.mk P.L (step R i per).sizes:Ratio B ff).residue (address l)
    let ranks:=fun l:I=>mass k (words l)
    let prior:=program (k:=k) old q words c (fun _=>site) (fun _=>t)
    whole ranks d S choose (fun u o r=>WilsonOriginalCensusRosterMenu.central R ranks N i q B prior digit u o.val place d r v)=
      WilsonOriginalCensusFiniteLedger.reading R N i per q d k old words c site t address choose S v:=by
  intro P ff B digit ranks prior
  by_cases run:S.Nonempty
  · let anchor:=choose S run
    let seats₀:=seats P (step R i per).sizes dvd_rfl dvd_rfl S address
      (fun _=>WilsonReceivedDepositedOrbitalNameWages.central ff) anchor
    let row:=ink S anchor.val (place anchor.val) (relative S anchor.val place)
    have backs:∀l∈S,Lattice.wrap B (seats₀ l)=Lattice.wrap B (row l):=
      WilsonNeutralTwoPrintPathBoardCentralSeats.original P (step R i per).sizes S anchor address
        (fun _=>WilsonReceivedDepositedOrbitalNameWages.central ff) place located
    have eqn:=(WilsonNeutralTwoPrintPathBoardSeam.original R N i per hi simple tag old q well width one bill
      words c live site t S digit seats₀ row backs d kept v).symm
    simpa only [whole,WilsonOriginalCensusFiniteLedger.reading,dif_pos run,WilsonOriginalCensusRosterMenu.central,
      diagonal,Complex.ofReal_sum,seats₀,row,anchor,digit,ranks,prior,P,ff,B] using eqn
  · simp only [whole,WilsonOriginalCensusFiniteLedger.reading,dif_neg run]

end YM.Integration.WilsonNeutralTwoPrintPathBoardCentral
end
