import YM.Integration.WilsonPointChildGazette
import YM.Integration.WilsonPointChildPairedHistory
import YM.Integration.WilsonPointChildCoveredRead
import YM.Integration.WilsonPointChildDigitLedger
import YM.Integration.WilsonPointChildWindingIncome
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPointChildDigitIncome
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
variable {G:Gauge}{d D:ℕ}

theorem original (R:Run G)(simple:G.Simple)(booked:WilsonPointChildFiledTest.Filed R)
    (u:G.ColorIndex)(depth:d<D)(o:Loc G 1)
    (tags:∀i n,(Flat.primary (R.family.path.levels.clock.op i 0).patch R.family.path.levels.clock.kernel n).Choices)
    (price:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices price R.kit)(E:ℕ){η:ℝ}(pos:0<η):
    ∀ᶠj:ℕ in atTop,∀N,j≤N→∀digit:∀i,Site (R.family.S.block i),∀v:Letter (R.family.labels.level d),∀p:Scroll D,
    let X:=WilsonPointChildDigitLedger.ledger R u depth digit N (N-j) j v p
    let A:=(R.family.path.levels.clock.hatBeta j)^η*‖physical p‖
    Auth d X ∧ ∀e≤E,∀r,Wig terrain (fun _:Unit=>0) (width R j) A {()} (X.2 e r) ∧
      ∀n x,|plume (X.2 e r) n x|≤A :=by
  let V:=R.family.path.levels
  filter_upwards [booked (routes R) u depth o E pos,V.fits.deep.eventually (eventually_ge_atTop d)] with j pay awake
  intro N live digit v p X A
  have enough:∀i:ℕ,j ≤ i → d ≤ V.clock.J (i+1):=fun i h=>awake.trans (V.fits.mono (by omega))
  have out:X.2=WilsonNeutralPointCourse.filed R (routes R) u depth digit N j v (physical p):=
    (WilsonPointChildDigitLedger.covered R u depth digit tags simple o price funded N (N-j) j (by omega) v p).trans
      (WilsonPointChildDigitReturn.original R u depth digit simple o _ _ _ (by omega) (fun i hi _=>enough i hi) _ _)
  have court:=WilsonNeutralPointCourse.original R (routes R) u depth digit N j simple o live
    (awake.trans (V.fits.mono (Nat.le_succ _)))
  refine ⟨WilsonPointChildDigitLedger.honest R u depth digit simple o _ _ _ (by omega) v p,?_⟩
  intro e he r
  rw [out]
  have invoice:=((pay N live).1 digit).every court v (physical p) e he r
  have ws:0≤width R j:=((Primer.FamilyWindow R.family).pos _).le
  exact ⟨WilsonPointChildCoveredTariff.tested _ () o ws invoice,WilsonPointChildWindingIncome.folded o ws invoice⟩
end YM.Integration.WilsonPointChildDigitIncome
