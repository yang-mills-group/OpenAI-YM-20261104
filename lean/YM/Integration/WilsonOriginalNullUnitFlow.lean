import YM.Integration.WilsonOriginalNullPhysicalHistory
import YM.OPE.Portfolio.Solemn

/-! At horizon zero, every dated emitted field is the literal scalar times
the same Wilson vacuum. This includes the true fine conditional means. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalNullUnitFlow
open Function Filter MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Relay
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext Repeat Legato Graces Roost Org Push.Local
open WilsonOriginalNullCorridor MergeProof.Ribbons.ManyCopies.Cadet.Studio.ZeroDegree
open scoped Classical BigOperators Topology Matrix.Norms.Frobenius
variable {G:Gauge}

theorem size {F:Frame G 0} (x:F.Coeff) : F.coeffSize x=‖x 0‖ := by
  unfold Frame.coeffSize
  apply Finset.sum_eq_single 0
  · intro i _ hi;exact (hi (one_at i)).elim
  · simp

theorem raw {F:Frame G 0} (S:SectionData F) {n:Side} (P:Rep G n) (o:Site n) (α:F.Coeff) :
    (primary o α).density o S P=(α 0) • (fun U=>(P.eval U:ℂ)) := by
  funext U
  have unit:=congrFun (unit_density S P o) U
  rw [primary_density] at unit
  rw [primary_density]
  have scaled:part S o P U α=(α 0)*(part S o P U F.e0) := by
    simpa only [map_smul,smul_eq_mul] using congrArg (part S o P U) (power_zero α)
  rw [scaled, mul_left_comm,unit];rfl

theorem vacuum (C:Family G) (H:C.Makes) (N p b n:ℕ) (z:ℂ) (live:b+n≤N) :
    flow C 0 N p b n (z • liftVac C.path N p (b+n)) = z • liftVac C.path N p b := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have step:b+n<N:=by omega
    have v:=vac_integrable C.path N p (b+n+1) H.wilson step
    have move:=vac_transfer C.path N p (b+n) H.wilson step
    change flow C 0 N p b n (GermGraph.transition (C:=C) 0 N p (b+n) (z • liftVac C.path N p (b+n+1)))=_
    rw [GermGraph.transition,blast,pow_zero,one_smul,StepData.push_smul _ _ _ z v,←move]
    exact ih (by omega)

end YM.Integration.WilsonOriginalNullUnitFlow
