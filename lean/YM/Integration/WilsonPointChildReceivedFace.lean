import YM.Integration.WilsonPointChildPlacedPortfolio
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPointChildReceivedFace
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
open WilsonPointChildPlacedIncome
open WilsonCoeffUV.Winding
variable {G:Gauge}{ι:Type}[DecidableEq ι]{D k:ι → ℕ}

def mounted (T:Finset ι)(old new:family G D):family G D:=
  fun J=>if J⊆T then old J else new J

theorem oldface (T J:Finset ι)(w:J⊆T)(old new:family G D):mounted T old new J=old J:=if_pos w

theorem newface (T J:Finset ι)(w:¬J⊆T)(old new:family G D):mounted T old new J=new J:=if_neg w

theorem legal (T:Finset ι){old new:family G D}(prior:Eu k old)(birth:Eu k new)(empty:old ∅=0):
    Eu k (mounted T old new) ∧ mounted T old new ∅=0:=by
  refine ⟨fun J=>?_,(oldface T ∅ (empty_subset _) old new).trans empty⟩
  by_cases inside:J⊆T
  · rw [oldface T J inside];exact prior J
  · rw [newface T J inside];exact birth J

def item (M z A:ℝ)(old new:ι → ℝ)(I:Finset ι):ℝ:=
  2*M*weights old I+(1+z)*A^I.card+weights new I

def allowance (M z A:ℝ)(old new:ι → ℝ)(I:Finset ι):ℝ:=
  1+∑J∈I.powerset,item M z A old new J

omit [DecidableEq ι] in
theorem budget (I:Finset ι)(M z A:ℝ)(old new:ι → ℝ)(mp:0 ≤ M)(zp:0 ≤ z)(ap:0 ≤ A)
    (op:∀s,0 ≤ old s)(np:∀s,0 ≤ new s):
    let C:=allowance M z A old new I
    1 ≤ C ∧ ∀J⊆I,J.Nonempty →
      let W:=weights (fun _=>C) J
      (2*M*weights old J+(1+z)*A^J.card ≤ W) ∧ (M*weights old J+A^J.card ≤ W) ∧ weights new J ≤ W:=by
  intro C
  have o₀(J:Finset ι):0 ≤ weights old J:=Finset.prod_nonneg (fun s _=>op s)
  have n₀(J:Finset ι):0 ≤ weights new J:=Finset.prod_nonneg (fun s _=>np s)
  have pos(J:Finset ι):0 ≤ item M z A old new J:=by
    unfold item;have h₁:=o₀ J;have h₂:=n₀ J;positivity
  have cp:1 ≤ C:=le_add_of_nonneg_right (Finset.sum_nonneg (fun J _=>pos J))
  refine ⟨cp,?_⟩
  intro J sub awake W
  have one:1 ≤ J.card:=Finset.card_pos.mpr awake
  have lift:item M z A old new J ≤ C:=(Finset.single_le_sum (fun L _=>pos L) (Finset.mem_powerset.mpr sub)).trans
    (le_add_of_nonneg_left zero_le_one)
  have raised:C ≤ W:=by
    change C ≤ ∏_s∈J,C
    simp only [Finset.prod_const]
    simpa only [pow_one] using pow_le_pow_right₀ cp one
  have all:2*M*weights old J+(1+z)*A^J.card+weights new J ≤ W:=lift.trans raised
  have first:(2*M*weights old J+(1+z)*A^J.card) ≤ W:=(le_add_of_nonneg_right (n₀ J)).trans all
  have C₁:0 ≤ M*weights old J:=mul_nonneg mp (o₀ J)
  have C₂:0 ≤ z*A^J.card:=mul_nonneg zp (pow_nonneg ap _)
  refine ⟨first,by nlinarith [first],?_⟩
  exact (le_add_of_nonneg_left (by have h₁:=o₀ J; positivity : 0 ≤ 2*M*weights old J+(1+z)*A^J.card)).trans all

end YM.Integration.WilsonPointChildReceivedFace
