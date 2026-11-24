import YM.Integration.WilsonPointChildWindingHistory
import YM.Integration.WilsonNeutralPointWeakIncome
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPointChildWindingHierarchy
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
variable {G:Gauge}

/-- The unfolded finite Wick program and the directly normalized covering
program use the same original group alphabet and the same child at each scale. -/
def Filed (R:Run G):Prop:=
  ∀(u:G.ColorIndex)(d E D:ℕ)(depth:d<D)(_o:Loc G 1),
  ∀tags:∀i n,(Flat.primary (R.family.path.levels.clock.op i 0).patch R.family.path.levels.clock.kernel n).Choices,
  ∀ᶠm:ℕ in atTop,∀N per,m ≤ N → 
  let n:=R.family.side m per
  ∀v:Letter (R.family.labels.level d),∀p:Scroll D,∀e ≤ E,∀r x,
    |WilsonPointChildFiniteReturn.table R u depth tags N (N-m) m v p n e r x-
      plume (WilsonPointChildCoverReturn.table R u depth N (N-m) m v p e r) n x| ≤ 
      (1+‖physical p‖)*rate R.family.path.levels m per

theorem original (G:Gauge):∃pay:ℕ → Gear G → ℝ,∀(R:Run G),G.Simple → 
    RG05Preconstruction.ReadoutPurchase R.b → FundedMarkedCoverRows.prices pay R.kit → 
    WilsonPointChildFiledTest.Filed R → WilsonNeutralPointForecast.Filed R.kit → 
    WilsonNeutralPointWeakForecast.Filed R.kit → ∀U:ℕ → ℕ,WilsonWindowFormalPurchase.Canonical U R.kit → Filed R:=by
  choose v result using fun e d=>WilsonPointChildWindingHistory.original G e d
  let pay(j:ℕ)(I:Gear G):=∑e∈range (j+1),∑d∈range (j+1),|v e d j I|
  refine ⟨pay,?_⟩
  intro R simple readout booked window strong weak U formal u d E D depth o tags
  let A:=R.family.path.levels
  have reaches:Tendsto (fun j=>A.clock.J (j+1)) atTop atTop:=
    A.fits.deep.comp (tendsto_add_atTop_nat 1)
  have quote:∀ᶠj:ℕ in atTop,∀I,v E d (A.clock.J (j+1)) I ≤ pay (A.clock.J (j+1)) I:=by
    filter_upwards [reaches.eventually (eventually_ge_atTop (max E d))] with j limit I
    let k:=A.clock.J (j+1)
    have hE:E∈range (k+1):=mem_range.mpr (by dsimp [k];omega)
    have hd:d∈range (k+1):=mem_range.mpr (by dsimp [k];omega)
    exact ((le_abs_self _).trans (single_le_sum (f:=fun d=>|v E d k I|) (fun _ _=>abs_nonneg _) hd)).trans
      (single_le_sum (s:=range (k+1)) (f:=fun e=>∑d∈range (k+1),|v e d k I|) (fun _ _=>Finset.sum_nonneg (fun _ _=>abs_nonneg _)) hE)
  have wallet:=WilsonNeutralPointWeakIncome.funded R (routes R) u depth o simple formal strong weak E
  have enroll:=result E d R simple readout pay booked quote window u depth o tags wallet
  filter_upwards [enroll] with m hearing
  intro N per live n v p e he r x
  have both:=WilsonPointChildPairedHistory.original R u depth tags simple o pay booked N (N-m) m (by omega) v p
  have yes:=(hearing N per live).2 v p e he r x
  change |(ledger R u depth N (N-m) m v p).1 n e r x-plume ((ledger R u depth N (N-m) m v p).2 e r) n x| ≤ _ at yes
  rw [both.1 n,both.2] at yes
  exact yes

end YM.Integration.WilsonPointChildWindingHierarchy
