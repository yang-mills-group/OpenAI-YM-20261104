import YM.Integration.WilsonPointChildCenteredLedger
import YM.Integration.WilsonPointChildCenteredPortfolio
import YM.Integration.WilsonPointChildPlacedFamily
import YM.Integration.WilsonVacuumPreResetMarkedFiledAtRun
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPointChildCenteredIncome
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

variable {G:Gauge}{ι:Type}{r:ℕ}{D:ι   →   ℕ}

open WilsonCoeffUV.Embroider.Canvas
open WilsonPointChildCenteredPortfolio (bank)
open WilsonPointChildCenteredFunctional (factor factor_nonneg)
def slack (h:ι → ℕ)(s:ι):ℝ:=∑t:Spring (h s),(1+WilsonPointChildCenteredSalary.bill t)
theorem slack_nonneg (h:ι → ℕ)(s:ι):0 ≤ slack h s:=sum_nonneg fun t _=>add_nonneg zero_le_one (WilsonPointChildCenteredSalary.nonnegative t)
def share (R:Run G)(m:ℕ)(η:ℝ)(h:ι → ℕ)(s:ι):ℝ:=
  1+(R.family.path.levels.clock.hatBeta m)^η*factor h s+slack h s

theorem original [Fintype ι](R:Run G)(simple:G.Simple)(booked:WilsonPointChildFiledTest.Filed R)
    (finite:WilsonPointChildDigitHierarchy.Filed R)(u:ι → G.ColorIndex){k h:ι → ℕ}(depth:∀s,k s<h s)(o:Loc G 1)
    (tags:∀i n,(Flat.primary (R.family.path.levels.clock.op i 0).patch R.family.path.levels.clock.kernel n).Choices)
    (cash:ℕ → Gear G → ℝ)(buy:FundedMarkedCoverRows.prices cash R.kit)(E:ℕ){η:ℝ}(positive:0<η):
    ∀ᶠm:ℕ in atTop,∀N per,m ≤ N  →  ∀(digit:ι  →  ∀i,Site (R.family.S.block i))(v:∀s,Letter (R.family.labels.level (k s)))(y:ι → Cover),
      let K:=bank R u depth digit N m v y
      let n:=R.family.side m per
      let a:=share R m η h
      Eu k K ∧ K ∅=0 ∧ (∀s,0<a s) ∧ ∀J,∀e ≤ E,∀r x,‖(repaint K J).1 n e r x‖ ≤ weights a J ∧
        ‖(K J).1 n e r x-(repaint K J).1 n e r x‖ ≤ rate R.family.path.levels m per*weights a J:=by
  let A:=R.family.path.levels
  have wet(s:ι):=WilsonPointChildCenteredLedger.rental R (u s) (k s) E h s (depth s) o tags simple cash buy booked positive
  have gap(s:ι):=WilsonPointChildCenteredSeat.original R (u s) (k s) E h s (depth s) o tags simple cash buy finite
  filter_upwards [eventually_all.mpr wet,eventually_all.mpr gap,(WardBin.bell A simple).eventually_ge_atTop 1] with m paid close fresh
  intro N per live digit v y K n a
  let H:=(A.clock.hatBeta m)^η
  have hn:0 ≤ H:=Real.rpow_nonneg (zero_le_one.trans fresh) _
  have bill(s):0 ≤ H*factor h s:=mul_nonneg hn (factor_nonneg _ _)
  have pos(s):0<a s:=by change 0<1+H*factor h s+slack h s;linarith only [bill s,slack_nonneg h s]
  have clean:=WilsonPointChildCenteredPortfolio.lawful R u depth o simple digit N m live v y
  refine ⟨clean.1,clean.2,pos,?_⟩
  intro J e he r x
  have τ:0 ≤ rate A m per:=(Real.exp_pos _).le
  by_cases single:J.card=1
  · obtain ⟨s,rfl⟩:=card_eq_one.mp single
    let X:=WilsonPointChildCenteredFunctional.seat R (u s) (k s) h s (depth s) (digit s) N m (v s) (y s)
    have eqK:K {s}=X:=by dsimp only [K,X,bank]; rw [WilsonPointChildPlacedFamily.singleton]
    change ‖(remade (K {s})).1 n e r x‖ ≤ _ ∧ ‖(K {s}).1 n e r x-(remade (K {s})).1 n e r x‖ ≤ _
    rw [eqK]
    simp only [weights,prod_singleton]
    have f:=paid s (digit s) N live (v s) e he r n x (y s)
    have d:=close s (digit s) N per live (v s) e he r x (y s)
    have left:H*factor h s ≤ a s:=by change _ ≤ 1+H*factor h s+slack h s;linarith only [slack_nonneg h s]
    have right:slack h s ≤ a s:=by change _ ≤ 1+H*factor h s+slack h s;linarith only [bill s]
    exact ⟨f.trans left,d.trans ((mul_le_mul_of_nonneg_right right τ).trans_eq (mul_comm ..))⟩
  have gone:K J=0:=other _ single
  change ‖(remade (K J)).1 n e r x‖  ≤  _ ∧ ‖(K J).1 n e r x-(remade (K J)).1 n e r x‖  ≤  _
  rw [gone,remake_zero]
  have cost:0 ≤ weights a J:=Finset.prod_nonneg fun s _=>(pos s).le
  simpa only [Prod.fst_zero,Pi.zero_apply,sub_zero,norm_zero] using And.intro cost (mul_nonneg τ cost)

end YM.Integration.WilsonPointChildCenteredIncome
