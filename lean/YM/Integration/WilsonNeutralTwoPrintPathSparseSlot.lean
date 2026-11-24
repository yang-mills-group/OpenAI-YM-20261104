import YM.Integration.WilsonOriginalSparseCofinalDatedSlot
import YM.Integration.WilsonNeutralTwoPrintPathSparseCenter
import YM.Integration.WilsonOriginalCensusFiledArmada
import YM.Integration.WilsonOriginalCensusCentralSheet

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonNeutralTwoPrintPathSparseSlot
open Function Finset Filter MeasureTheory Lattice Wilson RG Tree Marker QuadraticLocal Ac Source Labels
open QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Mentor QuadraticLocal.Affinity
open Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato AllOrder.Transit.WheelP
open AnalyticBridge VerifiedReset RemainderComparison Push Push.PriceCompiler Push.AbsoluteSums
open Stationary Comparison.RG02 QuadraticLocal.Rebirth VowsR LocalComparison ConnectedActivityE6
open OPE.Therm Multi WilsonRootedKioskOccupiedSlip WilsonOriginalSeparatedRegular
open WilsonOriginalSeparatedMask Comparison.Density.Transport Pert.Asymptotics
open WilsonOriginalCensusAngularFace
open scoped BigOperators Classical
open Function Filter Finset Lattice Laurent RG Wilson Stationary Primitives.TwoWave
open QuadraticLocal QuadraticLocal.Poetry QuadraticLocal.Sunrise QuadraticLocal.Earn QuadraticLocal.Sunrise.Aviary QuadraticLocal.Affinity
open Marker Next.SectorChange Multi Comparison.RG02 AllOrder AllOrder.Floe
open Further.PhysicalPeriodLimitF933 Macrame Shingle Precision Tree Exterior PhysicalNext.Repeat.Legato
open AllOrder.Ker AllOrder.Ker.Start AllOrder.Haiku AllOrder.Ink WilsonCoeffUV WilsonCoeffUV.Blue PowerSeries
open WilsonOlderFreshGraphVote WilsonNeutralRenderedColumn WilsonOlderFreshGraphArmada FVA1Physical.TwoReset
open WilsonVacuumPreResetStationaryChange WilsonOriginalPrimerReplicatedInk PhysicalForestMarkedRay PhysicalForestRay
open FreeResolvent WilsonVacuumPreResetDepositedGeometric WilsonVacuumPreResetDepositedLetters WilsonVacuumPreResetFiniteRegister
open WilsonOriginalPointCompactRoster WilsonOriginalThreeCopiedCharts
open scoped Classical BigOperators ContDiff Topology
open LocalComparison Comparison.RG02.Cumulants Comparison.RG02.Assembly Order AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open PertExtension Series WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank
open WilsonLimitConstruction Work.F08 FullQLocal FullQLocal.RenderedStep
open WilsonVacuumPreResetDepositedIntegrand WilsonOriginalOccupiedForestIntegral WilsonOriginalMeasuredOccupiedForest
open WilsonVacuumPreResetOriginalOutput (covered)
open WilsonOriginalRelativeFoldedQuiet (relative)
open WilsonOriginalEarnedUnaryDriver (driver)
open WilsonVacuumPreResetDatedDeposit (Issued)
open WilsonOriginalThreePurchasedRays (prescribed)
open WilsonOriginalMixedBlockRows WilsonRegisteredPairUnaryWallet WilsonOriginalCensusCopySlate
open WilsonOlderFreshGraphSlate (Copy)
open Filter AllOrder.Floe Comparison.RG02 FVA1Physical.TwoReset
open WilsonOriginalCopiedContraction
open scoped Topology
open QuadraticLocal.Rebirth FVA1Physical.TwoReset Further.PhysicalPeriodLimitF933 Macrame
open WilsonOriginalCensusDatedMaterial (Material words charts mounts)
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Wheel.Express WilsonCoeffUV.Embroider
open WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Soil WilsonCoeffUV.Wheel.Flooring
open Work.F08
open FundedMarkedPathSelection
open PhysicalNext.Repeat.Legato WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Embroider.Canvas
open ComparisonDensity.Address WilsonCoeffUV.Shard WilsonCoeffUV.Winding OriginalIssuedMarkedRows
open ActualRunAdmissionScales OriginalBareMarkedInvoice Filter Function
open WilsonOlderFreshConnectedRobe WilsonCoeffUV.Bank.Ticket
open WilsonOlderFreshConnectedRobe WilsonOlderFreshGraphSlate WilsonOlderFreshConnectedRoll
open WilsonOlderFreshConnectedPin WilsonOlderFreshConnectedAppointment FundedMarkedCoverRows
open WilsonCoeffUV.Bank.Ticket
open WilsonOlderFreshConnectedBirth WilsonCoeffUV.Blue WilsonCoeffUV.Bank.Mosaic.Near
open WilsonCoeffUV.Bank.Carp
open WilsonOlderFreshConnectedBinding
open QuadraticLocal.Poetry QuadraticLocal.Sunrise QuadraticLocal.Sunrise.Aviary Stationary
open WilsonOriginalPrimerReceipts WilsonNeutralTwoPrintPathJet
open Primitives.TwoWave AllOrder.Haiku AllOrder.Ink Response PertExtension.Series
open WilsonNeutralTwoPrintPathRoll WilsonOlderFreshConnectedAssembly
open Further.PhysicalPeriodLimitF933 Macrame Shingle AllOrder.Ker FVA1Physical FVA1Physical.TwoReset
open WilsonCoeffUV.Winding WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Bank.Mosaic.Near
open WilsonNeutralTwoPrintPathRead
open WilsonNeutralTwoPrintPathFixed (parcel)
open WilsonReceivedFixedDigitHistory (Digits)
open WilsonReceivedFixedDigitCanonical (fixed)
open OriginalMarkedSourceComet WilsonThermometerDeclaredSeeds
open WilsonNeutralTwoPrintPathQuoted (bill)
open WilsonOriginalMixedBlockRows WilsonRegisteredPairUnaryWallet Multi
open WilsonNeutralTwoPrintPathCensus (slates)
open WilsonNeutralTwoPrintPathDatedPolynomial (row sheet entry)
open WilsonReceivedCoverGrade (Same)
open FundedMarkedPathSelection (output)
open WilsonNeutralTwoPrintPathDatedPolynomial WilsonNeutralTwoPrintPeg
open WilsonCapturedRootedAngularSlots WilsonCapturedPrimaryWindingMaterialRead
open WilsonOriginalCensusDatedSheets (sideValue winding)
open WilsonNeutralTwoPrintPathCalendar (spent)
open WilsonOriginalCensusDatedWindingFare (price)
open Comparison.Density.Mirrors
open WilsonCapturedRootedAngularSlots WilsonCapturedPrimaryWindingMaterialRead WilsonNeutralTwoPrintPeg
open FVA1Physical FVA1Physical.TwoReset Further.PhysicalPeriodLimitF933 Macrame Shingle
open RegulatorIR RegulatorIR.Budget RegulatorIR.Diagram
open WilsonOriginalSparseFiledRanks (hull)
open WilsonOriginalSparseFiledOpening (near tail)
open WilsonOriginalSparseDatedHeld (Sample)

/-- The actual two filed rows at the physical sparse site. Their signed input is
the whole measured pupil against the already enrolled lower material. -/
theorem original
    {G:Gauge} (R:Run G) {m j N per k:ℕ}   (hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)   (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)(Q:D.Tab R.rolls)   (π:ℕ → Layout G)(Γ:ℕ → Pace.Coin)(Ψ:∀i,RG.Rep G (R.family.side i per))   {φ:ℕ → ℕ}(books:Mentor.Offices.Books D R.rolls Q φ)(base:m ≤ j)   (ahead:Mentor.Forecast D R.rolls Q φ books)   {n:ℕ}
    {S S': (Fin n) → ℝ}{a a':ℕ}
    (incomingHigh:Config G (R.family.side (j+1+1) per) → Marker.Poly (Stock.census (Fin n)))   (incomingLow:Config G (R.family.side (j+1) per) → Marker.Poly (Stock.census (Fin n)))
    (upper:WilsonOriginalDatedCensusInput.Filed (i:=j+1) (N:=N) R hk D Q π Γ Ψ books (Nat.le_succ_of_le base) ahead S a incomingHigh)   (lower:WilsonOriginalDatedCensusInput.Filed (i:=j) (N:=N) R hk D Q π Γ Ψ books base ahead S' a' incomingLow)
    (t:YM.Multi.Hot (Stock.census (Fin n))) (v:(Fin n)) (ceiling:ℕ)
    {I:Type}[Fintype I]{pu:Passport (R.family.side ((j+1)+1) per) (Fin n)}
    (B:I→Binder pu (Stock.census (Fin n))){qu:ℕ}{su:ℝ}
    (U:Material R N ((j+1)+1) qu upper.grades su B)
    (sites:Fin n → Cover) {ql:ℕ}{sl:ℝ}
    (L:Material R N (j+1) ql lower.grades sl (WilsonOriginalCensusFaceSites.binder (R.family.side (j+1) per) sites))
    (test:Case L.tests)(addressed:WilsonOriginalCensusFaceSheet.Addressed sites L test)
    (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)(live:(j+1)<N)
    (trees:∀b:Covers R.family.path.levels.S ((j+1)) ((R.family.side (j+1) per)),Forest (step R ((j+1)) b.val).ratio)
    (tags:∀b:Covers R.family.path.levels.S ((j+1)) ((R.family.side (j+1) per)),(step R ((j+1)) b.val).Choices)
    (κ:(v:(Fin n))→Knob (L.tests v))(pt:(Fin n)→Chamber)(top:ℕ)
    (cells:WilsonReceivedFixedDigitHistory.Digits R.family.path.levels (Fin n))
    (seed:(v:(Fin n))→Choice R lower.grades v)
    (_placed:((upper.post)).passport=pu)(_names:((upper.post)).modelIndex=((l:I)×(words U l).Roster))
    (_ink:HEq ((upper.post)).model (mounts U))
    (_pass:Pass D Q R.alloy R.kit)(_month:Scholar.Month R.rolls D Q R.alloy.delay)
    {quiet:ℕ→SeriesA G}(_actual:Read R N m (Burn.horizon k) quiet π Γ){τ cash:ℝ}
    (_funded:Issued R N ((j+1)+1) (Burn.horizon k) (quiet ((j+1)+1)) τ cash)
    (_fineLegal:Legal ((AllOrder.Floe.Step.tape (Burn.horizon k+2))) (π ((j+1)+1)))(_coarseLegal:Legal ((AllOrder.Floe.Step.tape (Burn.horizon k+2))) (π ((j+1))))
    (_fit:upper.order≤Burn.horizon k+1)(_orderU:upper.order≤qu)(_showShelf:upper.shelf≤R.alloy.B.a.clock.J ((j+1)))
    (r:ℕ)(_through:r≤upper.order)(_kept:∀e,e+(WilsonOriginalCensusPhysicalLoad.head (sides upper.grades lower.grades) t.val)<ceiling→e≤r)
    (calendar:WilsonOriginalCensusFixedBank.Income (k:=lower.grades) R κ pt ql (j+1))
    (younger:j+1<top)(valid:top≤N)
    (written:∀y J,output L.prior J N y=fixed R lower.grades κ pt N top (j+1) cells seed y J)
    (_placeL:lower.post.passport=WilsonOriginalCensusFaceSites.port (R.family.side (j+1) per) sites)
    (_namesL:lower.post.modelIndex=((l:YM.Multi.Hot (Stock.census (Fin n)))×(words L l).Roster))(_inkL:HEq lower.post.model (mounts L))
    (_keptL:∀e,e+(WilsonOriginalCensusPhysicalLoad.head (sides upper.grades lower.grades) t.val)<ceiling→e≤ql)(_wallet:lower.x=upper.x)
    (rates:WilsonOriginalCensusDatedHeldTariff.Rates R lower.grades κ pt (j+1) top ql)(atTop:top≤N)
    (within:WilsonOriginalCensusFaceAdmission.housed sites R (j+1) per)(gross wind:ℝ)
    (wallet:‖∏w∈t.val.val,(upper.x w).val‖*‖touch test t.val.val‖≤gross)
    (opened:∀e (paid:e≤ql),WilsonOriginalCensusDatedPeriodOpening.Opened R (j+1) per (mass lower.grades t.val.val+e)
      (rates.width t.val.val ⟨e,by omega⟩) (rates.fare t.val.val ⟨e,by omega⟩) gross wind)
    (power E:ℕ)
    (e:ℕ)(active:e+(WilsonOriginalCensusPhysicalLoad.head (sides upper.grades lower.grades) t.val)<ceiling)(Y:Stationary.Link G ((R.family.side (j+1) per)))(seen:WilsonOriginalSparseDatedHeld.Sample (((upper.post.passport.coarser (R.family.path.levels.clock.op (j+1) per).ratio).origin) v) (((Ψ (j+1))).p.B/32) (e+(WilsonOriginalCensusPhysicalLoad.head (sides upper.grades lower.grades) t.val)) Y)
    (measured:let repeated:=(Adjacent.born (fun a z=>(WilsonOriginalCensusCofinalCopies.value R live B (charts U) upper.x (R.family.side (j+1) per)
          dvd_rfl trees tags upper.order z a).part t.val)
        ((Rebirth.caliber (Γ (j+1)) (Oak.grade0 R hk D Q π Γ (Nat.le_succ_of_le base) upper.post.lesson)).back (Burn.horizon k+2)) 0 r e Y)
      ‖repeated-WilsonOriginalCensusDatedSheets.sideValue L κ pt top cells seed upper.x true t.val e
          (WilsonOriginalRawQReversion.coordinates G (R.family.side (j+1) per) Y)‖≤
        ((R.alloy.B.a.clock.hatBeta (j+1))^(near power (WilsonOriginalCensusPhysicalLoad.head (sides upper.grades lower.grades) t.val) E))⁻¹):
    WilsonOriginalSparseDatedCondition.heard R hk D Q π Γ Ψ books base ahead incomingHigh incomingLow upper lower t
      (AllOrder.Floe.Step.tape (Burn.horizon k+2)) power E wind e Y:=by

  obtain ⟨priorFit,honest,face⟩:=WilsonNeutralTwoPrintPathSparseCenter.original sites L test κ pt top
    cells seed upper.x addressed calendar younger valid written
  have stockU:=WilsonOriginalCensusFiledArmada.original U upper.post.model _placed _names _ink
    (fun _=>1) (fun _=>zero_lt_one) (order:=qu) (seats:=n+1) (shelf:=∑v,upper.grades v)
    le_rfl (by omega) (by omega) le_rfl
  have stockL:=WilsonOriginalCensusFiledArmada.original L lower.post.model _placeL _namesL _inkL
    (fun _=>1) (fun _=>zero_lt_one) (order:=ql) (seats:=n+1) (shelf:=∑v,lower.grades v)
    le_rfl (by omega) (by omega) le_rfl
  apply WilsonOriginalSparseCofinalDatedSlot.original R hk D Q π Γ Ψ books base ahead incomingHigh incomingLow
    upper lower t v ceiling B U sites L test addressed course live trees tags κ pt top cells seed
    _placed _names _ink stockU U.radius _pass _month _actual _funded _fineLegal _coarseLegal
    _fit _orderU _showShelf r _through _kept honest _placeL _namesL _inkL stockL L.radius
    _keptL _wallet priorFit rates atTop within gross wind wallet opened power E e active Y seen
  rw [←face t e Y]
  exact measured

end YM.Integration.WilsonNeutralTwoPrintPathSparseSlot
end
