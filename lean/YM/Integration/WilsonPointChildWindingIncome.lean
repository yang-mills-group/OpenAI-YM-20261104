import YM.Integration.WilsonPointChildGazette
import YM.Integration.WilsonPointChildPairedHistory
import YM.Integration.WilsonPointChildCoveredRead
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPointChildWindingIncome
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

theorem folded {α:Type}[Fintype α][DecidableEq α](o:α){s A:ℝ}(pos : 0 ≤ s)
    {r:ℕ}{T:Tile (Biglot α) r}(paid:Knoxville (fame α) s (0,o) T A)(n:Side)(x):
    |plume T n x|≤A:=by
  have tot:(∑' x,‖T x‖ₑ)≤ENNReal.ofReal A:=by
    simpa using directions paid pos (fun _=>1) 1 (by simp)
  have normed:‖plume T n x‖ₑ≤ENNReal.ofReal A:=calc
    _ ≤ ∑' y,‖peglet T n x y‖ₑ:=enorm_tsum_le_tsum_enorm
    _ ≤ ∑' y,‖T y‖ₑ:=ENNReal.tsum_le_tsum (fun y=>by by_cases h:slideC n y=x <;>simp [peglet,h])
    _ ≤ _:=tot
  exact (ENNReal.ofReal_le_ofReal_iff paid.1).mp (by simpa only [←Real.norm_eq_abs,ofReal_norm] using normed)

theorem original (R:Run G)(simple:G.Simple)(booked:WilsonPointChildFiledTest.Filed R)
    (u:G.ColorIndex)(depth:d<D)(o:Loc G 1)
    (tags:∀i n,(Flat.primary (R.family.path.levels.clock.op i 0).patch R.family.path.levels.clock.kernel n).Choices)
    (price:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices price R.kit)(E:ℕ){η:ℝ}(pos:0<η):
    ∀ᶠj:ℕ in atTop,∀N,j≤N→∀v:Letter (R.family.labels.level d),∀p:Scroll D,
    let X:=ledger R u depth N (N-j) j v p
    let A:=(R.family.path.levels.clock.hatBeta j)^η*‖physical p‖
    Auth d X ∧ ∀e≤E,∀r,Wig terrain (fun _:Unit=>0) (width R j) A {()} (X.2 e r) ∧
      ∀n x,|plume (X.2 e r) n x|≤A:=by
  filter_upwards [WilsonPointChildCoveredRead.original R simple booked u depth o E pos] with j upper
  intro N live v p X A
  have stage:j+(N-j)≤N:=by omega
  have out: X.2=WilsonPointChildCoverReturn.table R u depth N (N-j) j v p:=
    (WilsonPointChildPairedHistory.original R u depth tags simple o price funded N (N-j) j stage v p).2
  refine ⟨honest R u depth simple o _ _ _ stage v p,?_⟩
  intro e he r
  rw [out]
  have invoice:Knoxville (fame _) (width R j) (0,o) (WilsonPointChildCoverReturn.table R u depth N (N-j) j v p e r) A:=
    (upper N live v e he r).1 p
  have ws:0≤width R j:=((Primer.FamilyWindow R.family).pos _).le
  exact ⟨WilsonPointChildCoveredTariff.tested _ () o ws invoice,folded o ws invoice⟩

end YM.Integration.WilsonPointChildWindingIncome
