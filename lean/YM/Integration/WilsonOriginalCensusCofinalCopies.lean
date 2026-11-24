import YM.Integration.WilsonOriginalCensusStagedCopies
import YM.Integration.WilsonOriginalCensusGaussianCopies

/-! The copied original conditional before kinetic reversion, using all
licensed sets of the previously issued words and independent relative lifts. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusCofinalCopies
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
attribute [local instance] Gauge.frobInner
open WilsonOriginalMixedBlockRows WilsonRegisteredPairUnaryWallet WilsonOriginalCensusCopySlate
open WilsonOlderFreshGraphSlate (Copy)
open Filter AllOrder.Floe Comparison.RG02 FVA1Physical.TwoReset
open WilsonOriginalCopiedContraction
open scoped Topology
variable {G:Gauge}(R:Run G){j N per:ℕ}(hi:j < N){V I:Type}[DecidableEq V][Fintype V][Fintype I]
  {P:Passport (R.family.side (j+1) per) V}(B:I → Binder P (Stock.census V))
  (Z:I → (n:Side) → Site n → PChart G n)(x:Affinity.Wallet (room V))
  (grid:Side)(tiles:(R.family.side j per).val∣grid.val)
  (trees:∀b:Covers R.family.path.levels.S j grid,Forest (step R j b.val).ratio)
  (tags:∀b:Covers R.family.path.levels.S j grid,(step R j b.val).Choices)
local notation "J" => Stock.census V


open WilsonOriginalCensusStagedCopies (pupil earned)
open WilsonReceivedDepositedOrbitalConditioned (staged)

def page (r:ℕ)(u:Stationary.Link G grid)(d:ℕ)(c:Covers R.family.path.levels.S j grid):Poly (J):=
  let b:=AllOrder.Ker.convey (coverWin c.prop) u
  let A:=Stationary.arm G _ 1 b
  let K:=staged B R N j c.val hi (trees c) (tags c) (tiled R tiles c) x Z A r
  let full:=Order.observe (Stock.census (I×Fin (Pages (R.family.side (j+1) per) (fine R j c.val)))) r (Order.logMarked K) d
  (((Pages grid (R.family.side j c.val):ℕ):ℝ)⁻¹:ℝ) • Poly.inject (fun s=>
    earned B R j c.val s full)

def value (r:ℕ)(u:Stationary.Link G grid)(d:ℕ):Poly (J):=
  limUnder (coverFilter R.family.path.levels.S j grid) (page R hi B Z x grid tiles trees tags r u d)

theorem original (grades:V→ℕ)(shell:∀l n y,shellK (∑v∈(B l).mode.val,grades v) (Z l n y))
    (pure:∀l n y a,Pure (Z l n y a))(r:ℕ)(u:Stationary.Link G grid)(d:ℕ):
    WilsonOriginalCensusGaussianCopies.value R hi B Z x grid tiles trees tags r u d=
       value R hi B Z x grid tiles trees tags r u d:=by
  unfold value WilsonOriginalCensusGaussianCopies.value
  apply congrArg (limUnder (coverFilter R.family.path.levels.S j grid))
  funext c
  unfold WilsonOriginalCensusGaussianCopies.page page
  apply congrArg (fun K : Poly (J)=>(((Pages grid (R.family.side j c.val):ℕ):ℝ)⁻¹:ℝ) • K)
  let b:=AllOrder.Ker.convey (coverWin c.prop) u
  let A:=Stationary.arm G _ 1 b
  have actual:=WilsonReceivedDepositedOrbitalConditioned.original B grades R N j c.val hi (trees c)
    (tags c) (tiled R tiles c) x Z A (fun l y=>shell l _ y) (fun l y=>pure l _ y) r d
  refine actual.2.trans ?_
  ext s
  exact WilsonOriginalCensusCompatibleCopies.original (J) (pupil B) _ s

end YM.Integration.WilsonOriginalCensusCofinalCopies
end
