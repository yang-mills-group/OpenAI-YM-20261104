import YM.Integration.OriginalMarkedRunAction
import YM.Integration.WilsonPhysicalHistoryRetainedSpringRows

/-! The genuine previous Spring splits each numbered regular activity on its
original support. Its omitted activity has the original rooted estimate. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open Filter Lattice RG PhysicalNext.Repeat.Legato
open scoped Classical
variable {G : Gauge} (R : Run G) {N n j : ℕ} (hj : j<N)

theorem retained_rows {d : ℕ} (A : Comparison R (p:=n) hj d) :
    let P := R.family.path.rep N n j
    let Q := approximation R (p:=n) hj d
    let E := remainder R (p:=n) hj d
    Q = { P with activities := Q.activities } ∧
    Q.activities.reg = P.activities.reg ∧ E.reg = P.activities.reg ∧
    P.activities.E = Q.activities.E + E.E ∧
    Q.activities.forced = P.activities.forced ∧ Q.activities.K = P.activities.K ∧
    E.EBound P.p ((Real.sqrt 2*Pert.Asymptotics.regulatorRun R.family N n (j+1))^(d+1)) := by
  let S := ActualRunSpring.selected R N n j hj
  let P := R.family.path.rep N n j
  let Q := approximation R (p:=n) hj d
  let E := remainder R (p:=n) hj d
  let fee := (Real.sqrt 2*Pert.Asymptotics.regulatorRun R.family N n (j+1))^(d+1)
  change Q = {P with activities := Q.activities} ∧ Q.activities.reg = P.activities.reg ∧
    E.reg = P.activities.reg ∧ P.activities.E = Q.activities.E + E.E ∧
    Q.activities.forced = P.activities.forced ∧ Q.activities.K = P.activities.K ∧ E.EBound P.p fee
  have regs := GapsLocal.Renew.registries (GapsLocal.Renew.premium d) S.spring S.point
  have sites := congrArg Activities.reg S.output_activities
  have fields := congrArg Activities.E S.output_activities.symm
  have budget : R.alloy.B.a.budget j=P.p :=
    A.posterior.volume.trans (congrArg Rep.p S.coarse.symm)
  refine ⟨?_,regs.1.trans sites,regs.2.trans sites,fields.trans A.posterior.exacts,
    A.forced,A.charges,?_⟩
  · exact congrArg (fun V : Rep G (R.family.side j n) => {V with activities:=Q.activities}) S.coarse.symm
  · exact (congrArg (fun p=>E.EBound p fee) budget).mp A.posterior.cut.boundE

end YM.Integration.OriginalMarkedRunAction
