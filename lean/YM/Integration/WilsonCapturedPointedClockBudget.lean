import YM.Integration.WilsonPositionProgramMeasuredClockTariff
import YM.Integration.WilsonCapturedClockRankProjection

/-! The original pre-enrolled vacuum clock also pays each occupied Laurent
order. The pole adds exactly its numerical value to the income's angular rank. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonCapturedPointedClockBudget
open Function Filter Finset Lattice Laurent Bloch Wilson RG Precision Exterior Tree Matrix PowerSeries
open PhysicalNext.Repeat.Legato Comparison.RG02 FreeResolvent WilsonCoeffUV WilsonCoeffUV.Bank
open WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open WilsonCoeffUV.Winding WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Bank.Mosaic
open WilsonVacuumPreResetStationaryChange WilsonVacuumPreResetDepositedRay
open WilsonVacuumPreResetOriginalOutput Marker Multi
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
open WilsonVacuumPreResetTorusDeposit (bank)
open WilsonVacuumPreResetTorusGrade (evaluated)
open FVA1Physical.TwoReset (MassCall)
open AllOrder.Floe.Step
open AllOrder.Ker Primitives.TwoWave.RealSlice
open WilsonVacuumPreResetDatedDeposit (Issued)
open WilsonVacuumPreResetMeasuredCoin (Agrees)
open WilsonVacuumPreResetDepositedGeometric (source)
open QuadraticLocal.Earn AllOrder.Floe
open WilsonFiledPeriodSeam WilsonCoeffUV.Bank.Realm ActualRunAdmissionScales
open WilsonVacuumPreResetFiniteHeatCourse
open scoped Classical BigOperators
open WilsonVacuumPreResetDatedCourse (coin)
open FVA1Physical.TwoReset (massJets)
open AllOrder.Floe
open FVA1Physical.TwoReset (Prescription AffineMass)
open AllOrder.Floe.Step.PlanV
open PhysicalNext PhysicalNext.Repeat Legato WilsonLimitConstruction Next.Foundations
open WilsonSubmittedPeriodSeam (price weight Bill)
open QuadraticLocal.Rebirth QuadraticLocal.Faith Comparison.RG02.Adjacent
open WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Winding RegulatorIR
open Comparison.RG02.Moving Comparison.RG02.Moving.Path
open WilsonVacuumPreResetDatedCourse (coin)
open WilsonVacuumPreResetFiniteHeatStep FundedMarkedCoverRows
open PertExtension.Series PertExtension.Series.Tested PositionX.Jet

open WilsonPositionProgramMeasuredClockTariff WilsonCapturedClockRankProjection
open RegulatorIR.FVAAlt2.Booth
variable {G:Gauge}

theorem move (C:UnitCost)(pole i r:ℕ):
    Adjacent.money C (-(pole:ℤ)) i r=Adjacent.money C 0 i (r+pole):=by
  funext t
  simp only [Adjacent.money,Adjacent.tags,_root_.zpow_neg,zpow_natCast,zpow_zero,one_mul,pow_add,inv_pow]
  ring

theorem physical (R:Run G)(simple:G.Simple){N m e:ℕ}{Z:ℕ → SeriesA G}{π:ℕ → Layout G}{Γ:ℕ → Pace.Coin}
    (aligned:Agrees R N m e Z π Γ){j:ℕ}(low:m  ≤  j)(live:j < N)(origin:Γ j 0=0)
    (pole q r:ℕ)(room:q ≤ e+2)(P:ℕ→ℝ)(hp:∀i ≤ q,0 ≤ P i):
    charge ((QuadraticLocal.Rebirth.caliber (Γ j) origin).back (e+2)) (-(pole:ℤ)) q r P  ≤ 
      rimJ (ratioHigh (levels R) (ratio R) N j) q (r+pole) * ∑i∈range (q+1),P i:=by
  unfold charge
  rw [mul_sum]
  apply sum_le_sum;intro i hi
  rw [move]
  apply mul_le_mul_of_nonneg_right (measured R simple aligned low live origin room i (r+pole)) (hp i (mem_range_succ_iff.mp hi))

theorem registered (G:Gauge):∃v:ℕ → Gear G → ℝ,∃D:ℕ → ℕ,∀(R:Run G),G.Simple →
    FundedMarkedCoverRows.prices v R.kit → ∀s:ℕ,∀ᶠj:ℕ in atTop,
    ∀ {N m e:ℕ}{Z:ℕ → SeriesA G}{π:ℕ → Layout G}{Γ:ℕ → Pace.Coin},Agrees R N m e Z π Γ →
    m ≤ j → j < N → ∀(origin:Γ j 0=0)(pole q r:ℕ),q ≤ e+2 → q ≤ s → r+pole ≤ s →
    ∀(P:ℕ→ℝ), (∀i ≤ q,0 ≤ P i) →
      charge ((QuadraticLocal.Rebirth.caliber (Γ j) origin).back (e+2)) (-(pole:ℤ)) q r P  ≤ 
       (max 1 |zz R.family.path.levels j|)^(D s) * ∑i∈range (q+1),P i:=by
  obtain ⟨v,D,bank⟩:=calendar G
  refine ⟨v,D,?_⟩;intro R simple before s
  filter_upwards [bank R simple before s] with j paid
  intro N m e Z π Γ aligned low live origin pole q r room height slots P hp
  exact (physical R simple aligned low live origin pole q r room P hp).trans
    (mul_le_mul_of_nonneg_right (paid N live q height (r+pole) slots) (sum_nonneg fun i hi=>hp i (mem_range_succ_iff.mp hi)))

end YM.Integration.WilsonCapturedPointedClockBudget
