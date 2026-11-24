import YM.Integration.WilsonOriginalSoldCoverHearing
import YM.Integration.WilsonOriginalPrimerPostCover
import YM.Integration.WilsonOriginalReceivedCopiedCover
/-! Coefficient identity on the actual receiver's student and its original before-period input. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalSoldPostGaussian
open Function Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn
open QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Mentor Org
open AllOrder AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Transit WheelP
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Boulevard
open Push Push.PriceCompiler QuadraticLocal.Rebirth QuadraticLocal.Affinity ConnectedActivityE6
open AnalyticBridge VerifiedReset RemainderComparison LocalComparison Comparison.RG02
open WilsonOlderFreshGraphVote WilsonOlderFreshGraphArmada
open scoped Classical BigOperators Topology


open Function Filter Finset Lattice Laurent Bloch RG Precision Wilson FormalBulk08
open Next.Free Reef Flat Orb Wick Series Mesa Jets City Cork Bank Wine Dove Dove.Lab
open Exterior Stationary Lotus Shore Gorge Rift Lava Kemp
open Pose Glide Dawn Rial Roof Trellis Aster Borough Elm
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels PowerSeries
open PhysicalNext.Repeat.Legato Next.Foundations PhysicalNext PhysicalNext.Repeat
open RG.Supply Org QuadraticLocal QuadraticLocal.Sunrise QuadraticLocal.Sunrise.Aviary QuadraticLocal.Mentor Push.PriceCompiler
open Primer AllOrder AllOrder.Ink AllOrder.Floe Primitives.TwoWave QuadraticLocal.Poetry
open WilsonOlderFreshGraphSchool WilsonFundedWindowMenu WilsonWindowJointPurchase
open WilsonOlderFreshGraphPainter
open WilsonOriginalReceivedChain WilsonMeasuredRankedResidual Pert.Asymptotics
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open FVA1Physical.TwoReset Further.PhysicalPeriodLimitF933 Macrame Shingle QuadraticLocal.Earn Primitives.TwoWave
open WilsonNeutralRenderedColumn WilsonOriginalPrimerFiledPages
open WilsonMeasuredTransitionCatalogue
open WilsonMeasuredOriginalCatalogueUnion WilsonEmittedFiledGerm
open QuadraticLocal.Earn
open WilsonMeasuredJointCensusCash
open WilsonEmittedDictionary Comparison.Density Comparison.Density.Mirrors Comparison.Density.Transport
open WilsonLimitConstruction.FundedDictionaryPatchPrices
open WilsonEmittedOriginalReturn Push.AbsoluteSums
open WilsonOlderFreshPointRegistry

open MeasureTheory WilsonOlderFreshLocatedBook WilsonOlderFreshLocatedPayment
open WilsonOlderFreshLocatedRoster WilsonMeasuredPointHouseSeats
open WilsonOlderFreshGraphAllStages QuadraticLocal.Advent.Sycamore
open WilsonWindowBookPurchase WilsonWindowUniversalSchool
open scoped Classical BigOperators
open WilsonOlderFreshThermometerRoom WilsonOriginalPointCompactRoster WilsonOriginalPointCompactCash
open WilsonOlderFreshLocatedRoster WilsonOlderFreshPointRegistry

open WilsonOlderFreshThermometerCollector
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
variable {G:Gauge}(R:Run G)(wood:Primer.Families R.family)(a:hue G){Q m N i:ℕ}
    (dmax:Fin 3 → ℕ)(depth:∀v,WilsonOlderFreshThermometerRoom.weight v<dmax v)(σ:ℕ → ℝ)
    (digit:Fin 3 → ∀i,Site (R.family.S.block i))
    (T:WilsonOlderFreshThermometerSources.Table (m:=m) (N:=N) (Q:=Q) R dmax σ)(lo:m ≤ i)(hi:i<N)
    {I:Type}[Fintype I](owner:I → Fin 3)
    (columns:∀l,Letter (R.family.labels.level (WilsonOlderFreshThermometerRoom.weight (owner l))))
    (films:∀l,Studio (dmax (owner l))) (charge:I→ℂ)
    (per:ℕ)(sites:Fin 3→Site (R.family.side (i+1) per))(A:Fin 3→Set ℂ)(t:Wallet A)
local notation "T₁" => WilsonOlderFreshThermometerSources.selected R dmax σ T (lo.trans (Nat.le_succ i)) (Nat.succ_le_of_lt hi) owner columns films
local notation "Z₁" => WilsonOriginalThreeSoldCharts.charts R wood a dmax depth digit (Nat.succ_le_of_lt hi) owner columns films
local notation "grades" => WilsonOlderFreshThermometerRoom.weight
local notation "M" => WilsonOriginalPointCompactRoster.rows owner grades sites T₁ A charge
local notation "J" => Stock.census (Fin 3)

local notation "Copies" X:max => Covers R.family.path.levels.S i X
variable (grid:Side)(tiles:(R.family.side i per).val ∣ grid.val)
    (chosen : ∀ c : Covers R.family.path.levels.S i grid, Forest (R.family.path.levels.clock.op i c.val).ratio)
    (marked : ∀ c : Covers R.family.path.levels.S i grid, (R.family.path.levels.clock.op i c.val).Choices)
    (b:Stationary.Link G grid)


variable {k:ℕ}(hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
    (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)(Q₀:D.Tab R.rolls)
    (π:ℕ→Layout G)(Γ:ℕ→Pace.Coin)(Ψ:∀l,RG.Rep G (R.family.side l per))
    (route:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    {φ:ℕ→ℕ}(books:Mentor.Offices.Books D R.rolls Q₀ φ)(ahead:Mentor.Forecast D R.rolls Q₀ φ books)
    (pieces:Fin 3→Submodule ℝ ℂ)(order shelf seats:ℕ)
    (physical:Wallet A → Config G (R.family.side (i+1) per)→Poly (J))
    (P:WilsonOriginalReceivedChain.Post (N:=N) R hk D Q₀ π Γ Ψ books ahead A pieces grades order shelf seats i lo physical)
local notation "stud" => Oak.student (n:=per) R hk D Q₀ π Γ books lo P.op P.lesson ahead A P.model order P.voter
local notation "tape₀" => AllOrder.Floe.Step.tape (Burn.horizon k+2)

include route in
theorem original (sold:WilsonOlderFreshThermometerSources.Sold R wood a dmax depth σ digit T)
    (positive:0<σ (i+1))(bounded:∀v x,x∈A v→‖x‖≤1)(simple:G.Simple)
    (v:ℕ→Gear G→ℝ)(before:FundedMarkedCoverRows.prices v R.kit)(vac:FundedOriginalVacuumPaths.prices R.kit)
    (opened:WilsonOriginalPrimerPostCover.opening R simple v before vac k ≤ m)
    (path:PlanV.Path D R.alloy Q₀ (Burn.horizon k) N m π Γ)(pass:Pass D Q₀ R.alloy R.kit)
    (site:P.passport=Passport.point sites)(keys:P.modelIndex=WilsonOriginalPointCompactRoster.Index owner grades T₁)
    (same:HEq P.model (M))(r j:ℕ)(retained:r ≤ Q)(grade:r ≤ Burn.horizon k+2)(kept:r ≤ order)(tested:j ≤ r):
    Tendsto (WilsonOriginalSoldCoverHearing.phase R wood a dmax depth digit hi owner columns films charge per sites A t grid
      tiles chosen marked b r j) (coverFilter R.family.path.levels.S i grid)
      (𝓝 (peek tiles (stud) grades (π (i+1)) (tape₀) t j b)):=by
  obtain ⟨quiet,τ,fee,_,course,funded⟩:=WilsonOriginalPrimerPostCover.admitted R simple v before vac D Q₀ π Γ opened
    (le_trans lo (Nat.le_of_lt hi)) path pass lo hi
  have legal:Legal (tape₀) (π (i+1)):=by
    rw [P.lesson.ticket]
    exact AllOrder.Floe.Step.PlanV.audited R.rolls D _ _ _ P.lesson.entry
  have election:=WilsonOriginalReceivedCopiedCover.published R hk D Q₀ π Γ Ψ route books lo hi ahead A pieces grades
    order shelf seats physical P
  exact WilsonOriginalSoldCoverHearing.original R wood a dmax depth σ digit T lo hi owner columns films charge per sites
    A t grid tiles chosen marked b sold positive bounded course funded legal r order j retained grade kept tested
    P.model (stud) site keys same election

end YM.Integration.WilsonOriginalSoldPostGaussian
