import YM.Comparison.RG02.Bulk.Fk
import YM.Integration.WilsonPositionProgramGaussianRoute

/-! Signed changes of genuine submitted material in a finite Wilson block. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPositionProgramFiledGaussianChange
open Function Filter Finset MeasureTheory RG Precision Lattice Wilson Exterior Tree
open Next.SectorChange PertExtension.Series Multi Marker Comparison.RG02
open Next.Rank Comparison.RG02.Cumulants Comparison.RG02.Order
open Extra.Trajectories (connected)
open scoped BigOperators Classical
variable {G:Gauge}{c f:Side}{S:StepData c f}{p:Clip}{P:PathData G}{O:ChartRatio G}
  (K:Bulk.Kernel S p P O)(F:Forest S.ratio)(tag:S.Choices)
  {V:Type}[DecidableEq V][Fintype V]{R:Census V}

def drivers (W:Bulk.Colors R G f)(A:fieldDir G c 1)(r:ℕ):
    Hot (Board R r)→Normal.poly (Precision.Key F G):=
  Assembly.generator (Bulk.stage K F A) (Bulk.hinge F) W.power (Bulk.markFn S F W)
    (Bulk.geometric K F tag W) r

private theorem occupied {r:ℕ}(X:Grade R r)(h:UnitLeading X)(s:R.Mode)(live:s≠R.quiet)(t:Index r):
    (connected X).part (Join.pair s t)=(logMarked X).part (Join.pair s t):=by
  have vac:=congrArg (fun z:Grade R r=>z.part (Join.pair s t)) (log_vacant h)
  change (bottom R r (logVac X)).part (Join.pair s t)=(logVac X).part (Join.pair s t) at vac
  rw [bottom_value,if_neg live] at vac
  rw [log_full h,Poly.part_plus,←vac,zero_add]

def cofactor (W Y:Bulk.Colors R G f)(A:fieldDir G c 1)(r d:ℕ)(s:R.Mode)
    (anchor:Precision.Key F G→ℝ):Normal.poly (Precision.Key F G):=
  WilsonPositionProgramGaussianRoute.tally (K.covariance F tag) (K.symm F tag) 0
    (drivers K F tag W A r) (drivers K F tag Y A r) (Join.pair s (pick r d)) anchor Finset.univ.toList

theorem original (W Y:Bulk.Colors R G f)(A:fieldDir G c 1){d r:ℕ}(retained:d≤r)
    (s:R.Mode)(live:s≠R.quiet)(anchor:Precision.Key F G→ℝ):
    (d.factorial:ℂ)*((observe R r (logMarked (Bulk.Fk K F tag Y A r)) d).part s-
      (observe R r (logMarked (Bulk.Fk K F tag W A r)) d).part s)
      = ∫z,Cloud.paint z (cofactor K F tag W Y A r d s anchor) ∂Gaussian.cloud (K.covariance F tag):=by
  rw [mul_sub,observed (x:=logMarked (Bulk.Fk K F tag Y A r)) s retained,
    observed (x:=logMarked (Bulk.Fk K F tag W A r)) s retained,
    ←occupied _ (Bulk.fk_unit K F tag Y A r) s live,←occupied _ (Bulk.fk_unit K F tag W A r) s live]
  have bought:=WilsonPositionProgramGaussianRoute.integrated (K.covariance F tag) (K.symm F tag)
    (drivers K F tag W A r) (drivers K F tag Y A r) (Join.pair s (pick r d)) anchor (K.positive F tag).posSemidef 0
  simpa only [Bulk.Fk, Assembly.prescription, cofactor, drivers, Cloud.shift_zero, zero_add] using bought

end YM.Integration.WilsonPositionProgramFiledGaussianChange
end
