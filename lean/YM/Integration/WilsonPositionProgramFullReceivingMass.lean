import YM.Integration.WilsonPositionProgramReceivingMass
import YM.Integration.WilsonConditionalTaylorForestHaar

/-! Identification of the complete reset vacuum action on the actual received course and its finite sides. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPositionProgramFullReceivingMass
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

theorem filed {N m e j:ℕ}(Z:ℕ→SeriesA G)(π:ℕ→Layout G)(Γ:ℕ→Pace.Coin)
    (actual:Prescription R π Γ N m e)
    (declared:Prescription R (fun i=>bank (Z i)) (coin R N) N m e)
    (aligned:Agrees R N m e Z π Γ)(lower:m≤j)(next:j<N){t:ℕ}(rank:t≤e+2)(n:Side):
    WilsonFiledPeriodSeam.filed R N j n (Z j) t (e+2)=
    Pace.grouping (Γ j) (π j) (Step.tape (e+2)) (R.family.path.levels.params j).clip (R.alloy.B.kin.path N j) t n:=by
  have fine:m≤j+1:=by omega
  have smaller:j+1≤N:=next
  have same:AffineMass R next (bank (Z (j+1))) (π j) (Γ j) e:=
    FVA1Physical.TwoReset.mass_same R next (actual.legal (j+1) fine smaller)
      (declared.legal (j+1) fine smaller) (aligned.jets (j+1) fine smaller) (actual.step j lower next)
  have equality:=FVA1Physical.TwoReset.booked R next (bank (Z (j+1))) (π j) (bank (Z j)) (Γ j)
    (coin R N j) same (declared.step j lower next) rank
  exact congrFun equality.symm n

theorem original (simple:G.Simple)(fees:ℕ→Gear G→ℝ)(fund:FundedMarkedCoverRows.prices fees R.kit)
    (paths:FundedOriginalVacuumPaths.prices R.kit)(e:ℕ):
    ∃W:Credit,∀ᶠ m:ℕ in atTop,∀N,m≤N→∃Z:ℕ→SeriesA G,
      (∀i,m ≤ i → i ≤ N → ∃σ:ℝ,0<σ ∧ σ⁻¹≤zz R.family.path.levels i ∧
        Issued R N i e (Z i) σ (W.buy (zz R.family.path.levels i)+zz R.family.path.levels i*R.family.path.levels.clock.loopCap i)) ∧
      Prescription R (fun i=>bank (Z i)) (coin R N) N m e ∧
      ∀(D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)(Q:D.Tab R.rolls)
        (π:ℕ→Layout G)(Γ:ℕ→Pace.Coin),Step.PlanV.Path D R.alloy Q e N m π Γ→
        Step.PlanV.Spec D Q R.alloy R.kit→
        Agrees R N m e Z π Γ ∧ ∀j,m ≤ j → j < N → ∀ t, t ≤ e+2 → ∀n:Side,
          WilsonFiledPeriodSeam.filed R N j n (Z j) t (e+2)=
          Pace.grouping (Γ j) (π j) (Step.tape (e+2)) (R.family.path.levels.params j).clip (R.alloy.B.kin.path N j) t n:=by
  obtain ⟨W,property⟩:=WilsonVacuumPreResetMeasuredCoin.original R simple fees fund paths e
  refine ⟨W,?_⟩
  filter_upwards [property,WilsonConditionalTaylorForestHaar.ready R.family.path] with m purchased spacious
  intro N lower
  obtain ⟨Z,issued,planned,earned⟩:=purchased N lower
  refine ⟨Z,issued,planned,?_⟩
  intro D Q π Γ course audit
  have actions:=earned D Q π Γ course audit
  have physical:=FVA1Physical.TwoReset.authentic R π Γ D Q course audit (fun j lo _=>spacious j lo 0)
  refine ⟨actions,?_⟩
  intro j lo next t ht n
  exact filed R Z π Γ physical planned actions lo next ht n

end YM.Integration.WilsonPositionProgramFullReceivingMass
end
