import YM.Integration.WilsonPointChildCenteredFunctional
import YM.Integration.WilsonPointChildNamedPortfolio
import YM.Integration.WilsonPointChildNamedSalary
import YM.Integration.WilsonPointChildNamedRootSum
import YM.Integration.WilsonPointChildMixedQuote
import YM.Integration.WilsonPointChildReceivedFace
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPointChildCenteredPortfolio
open Function Filter Finset Lattice RG Wilson Laurent Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Wheel.ScaleS
open WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Embroider WilsonCoeffUV.Shard WilsonCoeffUV.Winding
open WilsonMarkedIndependentNormalizedElection (deck normalized)
open WilsonConditionalTaylorSeparatedPurchase (fee)
open scoped Classical BigOperators
open WilsonPointChildScalarSlot
open Filter Function Finset YM FormalBulk08 Lattice RG Laurent Next.Foundations PhysicalNext.Repeat.Legato
open Reef Flat Stationary Dawn Pose Kemp Palm Shore Mesa Wine Quire Roof Lotus Sierra Gorge Dove Rial Rift Lava
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Blue WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider WilsonCoeffUV.Embroider.Canvas
open WilsonPointChildTestCoordinates WilsonNeutralPointCourse WilsonPointChildCoverStep WilsonPointChildFiledPress
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open scoped ContDiff BigOperators Topology Classical ENNReal
open Function Filter Finset Matrix Lattice Wilson RG Laurent PowerSeries Work.F08
open FormalBulk08 Flat Reef Jets Orb Wick Stationary Series Shore Gorge Lotus Mesa Rift Lava Dawn Kemp Roof Sierra Rial
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Blue WilsonCoeffUV.Power
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Winding
open YM Next.Foundations PhysicalNext.Repeat.Legato Pose Palm Quire Wine Dove WilsonCoeffUV.Embroider
open WilsonPointChildTestCoordinates WilsonNeutralPointCourse WilsonPointChildCoverStep
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open scoped Classical Topology BigOperators ContDiff
open WilsonCoeffUV.Bank.Carp WilsonPointChildPairedHistory
open WilsonPointChildCoveredRead (directions)
open Function Filter Finset Lattice RG Wilson Laurent Precision PowerSeries
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos WilsonCoeffUV.Blue
open WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Winding WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Bank.Ticket
open WilsonVacuumPreResetFiniteHeatFinance (gross)
open WilsonVacuumPreResetFiniteHeatTable (table)
open WilsonMarkedIndependentNormalizedWallet (gap)
open WilsonMarkedIndependentNormalizedScale (rate)
open Next.Foundations PhysicalNext.Repeat.Legato
open scoped Classical BigOperators Topology
open Borough
open WilsonPointChildFiledSalary (inverseCost)
open WilsonPointChildFiniteRestamp (difference)
open WilsonPointChildCoverStep (routes)
open WilsonVacuumPreResetFiniteHeatFinance (gross)
open WilsonVacuumPreResetFiniteHeatTable (table)
open WilsonMarkedIndependentNormalizedScale (rate)
open WilsonCoeffUV.Bank.Carp
open WilsonPointChildFiniteStage (Gap)
open WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Bank.Carp
open WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Embroider WilsonCoeffUV.Shard
open WilsonCoeffUV.Wheel.Mark WilsonPointChildFiledPress WilsonPointChildWindingSchool
open WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Mer
open WilsonCoeffUV.Embroider.Canvas
open WilsonPointChildPlacedFamily
open WilsonVacuumPreResetMarkedOrdinaryBound (weights)
open private rooted from YM.Integration.WilsonPointChildWindingRoot

open WilsonPointChildPlacedIncome


open WilsonPointChildMixedGear

open WilsonPointChildMixedQuote WilsonPointChildReceivedFace
variable {G:Gauge} {ι:Type} [Fintype ι] [DecidableEq ι] {D k:ι → ℕ} {E m N:ℕ} {S:Finset ι}


open WilsonPointChildCenteredFunctional (factor factor_nonneg)
def cap (h:ι → ℕ):ℝ:=∑s,factor h s
omit [DecidableEq ι] in
theorem cap_nonneg (h:ι → ℕ):0≤cap h:=Finset.sum_nonneg fun _ _=>factor_nonneg _ _
def bank (R:Run G)(u:ι → G.ColorIndex){k h:ι → ℕ}(depth:∀s,k s<h s)(digit:ι → ∀i,Site (R.family.S.block i))(N j:ℕ)
    (v:∀s,Letter (R.family.labels.level (k s)))(y:ι → Cover):family G h:=
  roster (fun s=>WilsonPointChildCenteredFunctional.seat R (u s) (k s) h s (depth s) (digit s) N j (v s) (y s))

omit [Fintype ι] [DecidableEq ι] in
theorem lawful (R:Run G)(u:ι → G.ColorIndex){k h:ι → ℕ}(depth:∀s,k s<h s)
    (o:Loc G 1)(simple:G.Simple)(digit:ι → ∀i,Site (R.family.S.block i))(N j:ℕ)(live:j≤N)
    (v:∀s,Letter (R.family.labels.level (k s)))(y:ι → Cover):
    Eu k (bank R u depth digit N j v y) ∧ bank R u depth digit N j v y ∅=0:=
  ⟨legal _ (fun s=>WilsonPointChildCenteredFunctional.authorized R simple o (u s) (k s) h s (depth s) (digit s) N j live (v s) (y s)),
   other _ (by simp)⟩

omit [DecidableEq ι] in
theorem original (R:Run G)(simple:G.Simple)(booked:WilsonPointChildFiledTest.Filed R)
    (u:ι → G.ColorIndex){k h:ι → ℕ}(depth:∀s,k s<h s)(o:Loc G 1)
    (tags:∀i n,(Flat.primary (R.family.path.levels.clock.op i 0).patch R.family.path.levels.clock.kernel n).Choices)
    (price:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices price R.kit)(E:ℕ){η:ℝ}(pos:0<η):
    ∀ᶠj:ℕ in atTop,∀N,j≤N→∀digit:ι → ∀i,Site (R.family.S.block i),∀v:∀s,Letter (R.family.labels.level (k s)),∀y:ι → Cover,∀S w,w≤width R j→
    safeB y (bank R u depth digit N j v y) S E w ((R.family.path.levels.clock.hatBeta j)^η*cap h):=by
  have all:=eventually_all.mpr (fun s:ι=>WilsonPointChildCenteredFunctional.priced R simple booked (u s) (k s) h s (depth s) o tags price funded E pos)
  filter_upwards [all,(WardBin.bell R.family.path.levels simple).eventually_ge_atTop 1] with j paid clock
  intro N live digit v y S w hw J sub e he r
  let Q:ℝ:=(R.family.path.levels.clock.hatBeta j)^η
  have Qpos:0≤Q:=(Real.rpow_pos_of_pos (zero_lt_one.trans_le clock) _).le
  by_cases one:J.card=1
  · obtain ⟨s,rfl⟩:=card_eq_one.mp one
    simp only [bank,WilsonPointChildPlacedFamily.singleton,card_singleton,pow_one]
    have booked:=paid s N live (digit s) (v s) y e he r
    have hcap:factor h s≤cap h:=Finset.single_le_sum (fun t _=>factor_nonneg h t) (mem_univ s)
    exact (booked.shave hw).more (mul_le_mul_of_nonneg_left hcap Qpos)
  rw [bank,other _ one]
  exact (Wig.zero).more (pow_nonneg (mul_nonneg Qpos (cap_nonneg h)) _)
end YM.Integration.WilsonPointChildCenteredPortfolio
