import YM.Integration.WilsonSubmittedPeriodSeam
import YM.Integration.WilsonThermometerOriginalClockSlope

/-! The two leading position vacuum columns use the measured receiving action and its own kinetic clock. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPositionProgramReceivingMass
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

theorem bare_rates (simple:G.Simple){N j:ℕ}(next:j<N):
    coin R N j 0=0 ∧ coin R N j 1=0:=by
  let p:=pitch R.family.path.levels R.metals.O N j
  have native:=perch R.family.path.levels R.metals.O simple R.alloy.B.ratio next
  have first:constantCoeff p=1:=native.calm
  have second:coeff 1 p=0:=native.parityC 1 (by decide)
  change coeff 0 (p-1)=0 ∧ coeff 1 (p-1)=0
  rw [map_sub,map_sub,coeff_zero_eq_constantCoeff_apply,first,coeff_one,coeff_one,second]
  norm_num

private theorem factor_head (p q:Pace.Coin)(B:Pace.Scene G){k:ℕ}(n:Side)
    (h:∀j≤k,p j=q j):Pace.factor p B k n=Pace.factor q B k n:=by
  simp only [Pace.weighs]
  apply Finset.sum_congr rfl
  intro j hj
  rw [h j (by have:=Finset.mem_range.mp hj; omega)]

theorem grouping (p:Pace.Coin)(h₀:p 0=0)(h₁:p 1=0)(π:Layout G)
    (T:Finset Age)(B:Clip)(K:PathData G){k:ℕ}(first:k≤1)(n:Side):
    Pace.grouping p π T B K k n=Pace.grouping 0 π T B K k n:=by
  have h (j:ℕ)(hj:j≤k):p j=(0:Pace.Coin) j:=by
    have hi:j≤1:=hj.trans first
    interval_cases j <;> assumption
  have born (s:Age)(j:ℕ)(hj:j≤k):
      Pace.ladder (Pace.elapsed s) p j=Pace.ladder (Pace.elapsed s) 0 j:=by
    have hi:j≤1:=hj.trans first
    interval_cases j
    · rw [Pace.start _ h₀,Pace.start _ (q:=0) rfl]
    · rw [Pace.next _ h₀ h₁,Pace.next _ (q:=0) rfl rfl]
  simp only [Pace.grouping,Pace.shiftB,Pace.glory,Pi.add_apply,Finset.sum_apply]
  rw [factor_head p 0 _ _ h]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  exact factor_head _ _ _ _ (born s)

theorem original (simple:G.Simple){N m j e p:ℕ}(Z:ℕ→SeriesA G)(π:ℕ→Layout G)(Γ:ℕ→Pace.Coin)
    (aligned:Agrees R N m e Z π Γ)(lower:m≤j)(next:j<N)(t:ℕ)(first:t≤1):
    WilsonFiledPeriodSeam.filed R N j (R.family.side j p) (Z j) t (e+2)=
    Pace.grouping (Γ j) (π j) (Step.tape (e+2)) (R.family.path.levels.params j).clip (R.alloy.B.kin.path N j)
      t (R.family.side j p):=by
  obtain ⟨h₀,h₁⟩:=bare_rates R simple next
  have actual:=aligned.rates j lower next
  have a₀:Γ j 0=0:=(actual 0 (by omega)).trans h₀
  have a₁:Γ j 1=0:=(actual 1 (by omega)).trans h₁
  let n:=R.family.side j p
  let clip:=(R.family.path.levels.params j).clip
  let path:=R.alloy.B.kin.path N j
  change Pace.grouping (coin R N j) (bank (Z j)) (Step.tape (e+2)) clip path t n=_
  rw [grouping (coin R N j) h₀ h₁ _ _ _ _ first n,grouping (Γ j) a₀ a₁ _ _ _ _ first n]
  exact congrFun (aligned.jets j lower next.le t (by omega)).symm n

end YM.Integration.WilsonPositionProgramReceivingMass
end
