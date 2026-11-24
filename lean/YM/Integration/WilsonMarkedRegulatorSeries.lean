import YM.Integration.WilsonMarkedRegulatorGaugeRays

/-! Graded scalar evaluation of the actual finite regulator polynomial. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMarkedRegulatorSeries
open Filter Finset Lattice Wilson PertExtension PertExtension.Series PertExtension.Series.Tested RG
open FormalBulk08 FormalBulk08.Orb Jets Reef Stationary AllOrder AllOrder.Response AllOrder.Laplace.SigmaP
open RegulatorIR RegulatorIR.Ward RegulatorIR.Laplace RegulatorIR.Binding RegulatorIR.Prim
open RegulatorIR.Diagram RegulatorIR.Diagram.Formal RegulatorIR.Quadratic PowerSeries PositionX.Jet
open WilsonFormalGaugeCurve
open scoped Classical Topology BigOperators ContDiff
variable {I:Type}[Fintype I]

theorem coefficient (v:ℝ→I→ℝ)(hv:ContDiffAt ℝ ω v 0)(P:Pap I)(k:ℕ):
    coeff k (ocean (churn v) P)=weigh v (evaluation P) k:=by
  have active:RegulatorIR.Ward.Lift v:=by
    intro i
    have h:ContDiffAt ℝ ω (fun t=>v t i) 0:=(contDiffAt_apply ..).comp 0 hv
    exact h.of_le le_top
  rw [submerge,Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j=>coeff j (churn v (coeff i P))) k]
  unfold weigh
  apply Finset.sum_congr rfl
  intro j _
  have paid:=ink v active (coeff j P)
  have old:=needed (smooth v hv (coeff j P))
  apply congrFun (Aspiration.unique paid ?_)
  simpa only [WilsonFormalGaugeCurve.evaluation,traceP,MvPolynomial.aeval_eq_eval,Function.comp_def] using old

end YM.Integration.WilsonMarkedRegulatorSeries
end
