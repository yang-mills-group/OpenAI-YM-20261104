import YM.Integration.WilsonVacuumPreResetMeasuredCoin

/-! The chronological finite vacuum on the same Wilson ledger and held directions. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPositionProgramSubmittedQuiet
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
variable {N m j e p:ℕ} (Z:ℕ→SeriesA G)(π:ℕ→Layout G)(Γ:ℕ→Pace.Coin)
variable (aligned:Agrees R N m e Z π Γ)(lower:m≤j)(hj:j<N)
variable (F:Forest (step R j p).ratio)(tag:(step R j p).Choices)
variable {T:Type}[DecidableEq T][Fintype T]{J:Census T}(Q:Bulk.Colors J G (fine R j p))
local notation "program" => (RunFormalChain.fromRun R).step N j p hj
local notation "current" => QuadraticLocal.Fk.grant (π (j+1)) (Step.tape (e+2)) Q
open WilsonCoeffUV.Blue (flash)

include aligned lower in
theorem original (simple:G.Simple){σ C:ℝ}(hi:Issued R N (j+1) e (Z (j+1)) σ C)
    (x y:Stationary.Link G (coarse R j p))(t:ℕ)(ht:t≤e+2):
    Symmetry.Orbit.ground program F tag current (e+2) t (Stationary.arm G _ 1 x) -
    Symmetry.Orbit.ground program F tag current (e+2) t (Stationary.arm G _ 1 y)=
      -(diff (output R N j p) t (flatten (Stationary.arm G _ 1 x)) (flatten (Stationary.arm G _ 1 y)):ℂ):=by
  have right (a:Stationary.Link G (coarse R j p)):
      Symmetry.Orbit.ground program F tag current (e+2) t (Stationary.arm G _ 1 a)=
      held R N j p hj F tag (Z (j+1)) Q (e+2) (Stationary.arm G _ 1 a) (e+2) t:=by
    unfold held Symmetry.Orbit.ground
    rw [aligned.marked j lower hj p F tag Q a (e+2) le_rfl]
  rw [right x,right y]
  let U:=filed R N j p (Z (j+1))
  let E:=covered R N j p
  have kp:(income R N j p).path=R.alloy.B.kin.path N (j+1):=(RunFormalChain.fromRun R).selected N p (j+1) hj
  have kb:(income R N j p).clip=((levels R).params (j+1)).clip:=(RunFormalChain.fromRun R).clips N p (j+1) hj
  have filedRows (a:ℕ)(ha:a<3+e)(l:ℕ):U a (l+1)=E a (l+1):=by
    unfold U filed
    rw [kp,kb]
    exact hi.periodic a ha (fine R j p) l
  have head:=WilsonVacuumPreResetDepositedPhase.head R N j p hj (Z (j+1)) simple (filedRows 0 (by omega))
  have price (a:ℕ)(ha:a<3+e):coeff a (Blue.flash U-Blue.flash E)=
      MvPolynomial.C (MvPolynomial.eval 0 (coeff a (Blue.flash U-Blue.flash E))):=
    WilsonVacuumPreResetFoldedInlet.fieldIndependent U E a
      (WilsonLimitConstruction.FundedSpringPeriodGerm.grade _ _ _ _) (filedRows a ha)
  exact WilsonVacuumPreResetOriginalOutput.original R N j p hj F tag (Z (j+1)) head Q ((levels R).budget (j+1))
    (e+2) hi.positive hi.purchase hi.lower (fun a ha=>by have h:=hi.upper a ha; omega) simple (3+e) price (Stationary.arm G _ 1 x) (Stationary.arm G _ 1 y) (e+2) t ht (by omega)

end YM.Integration.WilsonPositionProgramSubmittedQuiet
end
