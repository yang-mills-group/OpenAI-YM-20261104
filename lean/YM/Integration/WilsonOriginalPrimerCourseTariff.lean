import YM.Integration.WilsonOriginalPrimerPostCover
import YM.Integration.WilsonVacuumPreResetMeasuredCaliber

/-! The occupied quiet, source and reversion tariffs for one complete physical run. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPrimerCourseTariff
open Function Filter Finset Lattice Laurent Bloch Wilson RG Precision Exterior Tree Matrix PowerSeries
open PhysicalNext.Repeat.Legato Comparison.RG02 FreeResolvent WilsonCoeffUV WilsonCoeffUV.Bank
open WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open WilsonCoeffUV.Winding WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Bank.Mosaic
open WilsonVacuumPreResetStationaryChange WilsonVacuumPreResetDepositedRay
open WilsonVacuumPreResetOriginalOutput Marker Multi
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
attribute [local instance] Gauge.frobInner
variable {G:Gauge}(R:Run G)

open WilsonVacuumPreResetTorusDeposit (bank)
open WilsonVacuumPreResetTorusGrade (evaluated)
open FVA1Physical.TwoReset (MassCall)
open AllOrder.Floe.Step
open AllOrder.Ker Primitives.TwoWave.RealSlice

open WilsonVacuumPreResetDatedDeposit (Issued)
open FVA1Physical.TwoReset (AffineMass)
open PertExtension.Series PowerSeries
open AllOrder AllOrder.Floe

open AllOrder.Floe.Step.PlanV FVA1Physical.TwoReset
open WilsonVacuumPreResetDatedCourse (coin)
open Primitives.TwoWave.RealSlice


open WilsonVacuumPreResetMeasuredCoin (Agrees)
open WilsonOriginalOccupiedForestIntegral (numerator)
open Next.SectorChange MeasureTheory


open PhysicalNext.Repeat RG.Supply Org QuadraticLocal.Mentor AllOrder.Transit.WheelP Filter
open QuadraticLocal QuadraticLocal.Advent QuadraticLocal.Rebirth Pressure PhysicalNext.Repeat.Legato
open AllOrder.Transit
open WilsonOriginalPrimerPostCover WilsonOriginalMeasuredOccupiedForest
open WilsonMarkedKineticDefect WilsonMarkedKineticGerm

variable (simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (paths:FundedOriginalVacuumPaths.prices R.kit)(k:ℕ)

def fare := Classical.choose (WilsonOriginalMeasuredOccupiedForest.original R simple v funded paths (Burn.horizon k))

variable {m N k:ℕ}
theorem retained (lower:opening R simple v funded paths k ≤ m)(mN:m≤N):
    ∃Z:ℕ→SeriesA G,
      (∀j,m≤j→j≤N→∃σ:ℝ,0<σ ∧ σ⁻¹≤zz (levels R) j ∧ Issued R N j (Burn.horizon k) (Z j) σ
        ((fare R simple v funded paths k).buy (zz (levels R) j)+zz (levels R) j*(levels R).clock.loopCap j)) ∧
      Prescription R (fun i=>bank (Z i)) (coin R N) N m (Burn.horizon k) ∧
      ∀(D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)(T:D.Tab R.rolls)
        (π:ℕ→Layout G)(Γ:ℕ→Pace.Coin),PlanV.Path D R.alloy T (Burn.horizon k) N m π Γ→Pass D T R.alloy R.kit→
        Read R N m (Burn.horizon k) Z π Γ ∧
        ∀ (i : ℕ), m ≤ i → i < N → ∃ start : Γ i 0 = 0, ∀ l ≤ Burn.horizon k+2, ∀ birth angular,
          physicalWeight (Rebirth.caliber (Γ i) start) (Burn.horizon k+2) l birth angular =
          formalWeight (pitch (levels R) (ratio R) N i) l birth angular:=by
  let dates:=Classical.choose_spec (WilsonOriginalMeasuredOccupiedForest.original R simple v funded paths (Burn.horizon k))
  obtain ⟨Z,banks,policy,courses⟩:=(eventually_atTop.mp dates).choose_spec m lower N mN
  refine ⟨Z,banks,policy,?_⟩
  intro D T π Γ path pass
  have read:=courses D T π Γ path pass.formal
  refine ⟨read,?_⟩
  intro i lo hi
  obtain ⟨_,_,_,left⟩:=banks i lo hi.le
  obtain ⟨_,_,_,right⟩:=banks (i+1) (by omega) hi
  have start:Γ i 0=0:=(read.course.rates i lo hi 0 (Nat.zero_le _)).trans
    (WilsonVacuumPreResetDatedCourse.affine R simple hi left right).1
  exact ⟨start,(WilsonVacuumPreResetMeasuredCaliber.settled R read.course lo hi start).2.2.2⟩

end YM.Integration.WilsonOriginalPrimerCourseTariff
