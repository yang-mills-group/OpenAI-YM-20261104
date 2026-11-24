import YM.Integration.WilsonPointChildWindingSchool
import YM.Integration.WilsonMarkedIndependentMixedSpatial
import YM.WilsonCoeffUV.Marked.Bounds.Independent
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPointChildDigitRoot
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
variable {G:Gauge}{α ι:Type}{r d D:ℕ}

private theorem rooted {T:Ten ℝ (Cloth α) r}{s A:ℝ}(positive:0 ≤ s)
    (paid:Wig terrain (fun _:Unit=>0) s A {()} T):Cork terrain 0 s A T:=by
  refine ⟨paid.1,fun x=>(paid.2 x).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonpos_left (Nat.cast_le.mpr ?_) (neg_nonpos.mpr positive))) paid.1)⟩
  let go:Fin (r+1)  →  ({()} : Finset Unit)⊕Fin r:=Fin.cases (.inl ⟨(),mem_singleton_self _⟩) .inr
  have chosen (j:Fin (r+1)):foyer (fun _:Unit=>0) {()} x (go j)=stud 0 x j:=
    Fin.cases rfl (fun _=>rfl) j
  apply league_le
  intro j k
  rw [←chosen j,←chosen k]
  exact leg_le ..

theorem priced (X:Era G ℝ)(z:Cover)(n:Side)(e r:ℕ){b A C:ℝ}(positive:0<b)
    (h:Wig terrain (fun _:Unit=>0) b A {()} (X.2 e r))(fold:∀x,|plume (X.2 e r) n x|≤A)
    (gap:∀x,|X.1 n e r x-plume (X.2 e r) n x|≤C):
    let Y:=shifted X z
    Wig terrain (fun _:Unit=>z) b A {()} (Y.2 e r) ∧
      (∀x,|plume (Y.2 e r) n x|≤A) ∧ ∀x,|Y.1 n e r x-plume (Y.2 e r) n x|≤C:=by
  intro Y
  refine ⟨abreast _ (fun _:Unit=>z) () (Cork.turn _ (rooted positive.le h)) positive.le,?_,?_⟩
  · intro x
    change |plume (revolve z (X.2 e r)) n x|≤A
    rw [plume_shift]
    exact fold _
  · intro x
    change |revolve (wrap n z) (X.1 n e r) x-plume (revolve z (X.2 e r)) n x|≤C
    rw [plume_shift]
    exact gap _
end YM.Integration.WilsonPointChildDigitRoot
