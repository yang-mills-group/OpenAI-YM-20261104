import YM.Integration.WilsonReceivedDepositedOrbitalWindingSeat
import YM.Integration.WilsonNeutralTwoPrintPathFineSubmission

noncomputable section
namespace YM.Integration.WilsonNeutralTwoPrintPathBoardSeam
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

/-- On the finite physical board, each retained old binder can use any lift
of its own actual parent.  All subfaces share the original quiet and reset. -/
theorem original (R:Run G)(N i per:ℕ)(hi:i<N)(simple:G.Simple)(tag:(step R i per).Choices)
    (old:Outerm G D)(q:ℕ)(well:Wellness k old){σ C:ℝ}(width:0<σ)(one:1≤C)(bill:CoverBill old q σ C)
    (J:I→Finset (Fin n))(c:I→Fin n)(live:∀l,c l∈J l)(site:Fin n→Lattice.Cover)(t:Case D)
    (S:Finset I)(digit:I→Site (loose (levels R) i).L)(y z:I→Lattice.Cover)
    (same:∀l∈S,Lattice.wrap (coarse R i per) (y l)=Lattice.wrap (coarse R i per) (z l))
    (d:ℕ)(kept:d≤q)(v:Stationary.Link G (coarse R i per)):
    let ranks:=fun l=>mass k (J l)
    let oldFile:=program (k:=k) old q J c (fun _=>site) (fun _=>t)
    let val:=fun w:I→Lattice.Cover=>Complex.ofReal (diagonal (mass ranks S+d)
      (fun r pos=>touch (@reading I) S ((spent R ranks N i q (coarse R i per) oldFile w digit S) d r pos))
      ((coordinates G (coarse R i per)) v))
    val y=val z:=by
  intro ranks oldFile val
  let P:=loose (levels R) i
  let fineSide:=fine R i per
  let F:=repeatF (step R i per)
  let reader:=@WilsonReceivedDepositedOrbitalFixedMoments.reading I
  let test:=fun l:I=>(touch t (J l)).smulRight WilsonReceivedDepositedOrbitalFixedMoments.point
  let upper:=fun w:I→Lattice.Cover=>chartIn P w digit
  let filed:=submit oldFile ranks q
  have sameFine (l:I)(hl:l∈S):Lattice.wrap fineSide (upper y l)=Lattice.wrap fineSide (upper z l):=by
    change Lattice.wrap fineSide (P.L.val • y l+Lattice.lift (digit l))=
      Lattice.wrap fineSide (P.L.val • z l+Lattice.lift (digit l))
    rw [map_add,map_add,←(Ratio.mk P.L (step R i per).sizes:Ratio (coarse R i per) fineSide).embed_wrap,
      ←(Ratio.mk P.L (step R i per).sizes:Ratio (coarse R i per) fineSide).embed_wrap,same l hl]
  have saved:=WilsonNeutralTwoPrintPathInheritedBlocks.original old well width one bill J c live (fun _:I=>site) test
  have printed:Wellness ranks filed:=(WilsonReceivedCompactVerseEntrance.original oldFile saved.2.1 width saved.1 saved.2.2).2.1
  have entries (T:Finset I)(sub:T⊆S):Through q ((filed (upper y) T).1 fineSide) ((filed (upper z) T).1 fineSide):=by
    have first:=WilsonNeutralTwoPrintPathFineSubmission.entry old well width one bill J c live (fun _:I=>site) test
      S T sub fineSide (upper y) (upper y) (fun _ _=>rfl)
    have last:=WilsonNeutralTwoPrintPathFineSubmission.entry old well width one bill J c live (fun _:I=>site) test
      S T sub fineSide (upper y) (upper z) sameFine
    exact fun a ha=>(first a ha).symm.trans (last a ha)
  have coupled:=WilsonReceivedDepositedOrbitalFilteredStep.original R N i per hi F simple tag (q+1)
    (filed (upper y)) (filed (upper z)) (printed.level' _) (printed.level' _)
    (printed.quiet' _) (printed.quiet' _) reader S (fun T sub a ha=>
      WilsonNeutralTwoPrintPathFineForest.paid R N i per hi F T _ _ 
        (WilsonNeutralTwoPrintPathFineGrades.ordinary T (fun U part=>entries U (part.trans sub))) reader a
        (Nat.le_of_lt_succ ha))
  have measured:=congrArg (fun u:POL (Woods G (coarse R i per))=>(MvPolynomial.eval ((coordinates G _) v) u:ℂ))
    (coupled d (Nat.lt_succ_of_le kept))
  have physical (w:I→Lattice.Cover):=WilsonOriginalCensusFinitePortrait.submitted R N i per hi ranks reader simple
    q oldFile saved.2.1 width saved.1 saved.2.2 w digit S d v
  exact (physical y).symm.trans (measured.trans (physical z))

end YM.Integration.WilsonNeutralTwoPrintPathBoardSeam
end
