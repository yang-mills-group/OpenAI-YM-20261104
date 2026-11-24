import YM.Integration.FVA1Physical.Wilson.FirstMarkedMoment
import YM.Integration.FVA1Physical.Wilson.WickFullTable

/-! The first positive coupling order of two physical colored inputs with the
same leading source. The cubic action, Haar and loop vertices drop out of
their difference without a volume bound on the unmarked vacuum action. -/
set_option autoImplicit false
set_option maxHeartbeats 1700000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter MeasureTheory Lattice RG Exterior Tree Precision Marker Multi
open YM.Primitives.GCC.Anchor YM.Next.SectorChange YM.Extra.Trajectories Comparison.RG02 Assembly Order
open scoped Topology Classical ContDiff BigOperators
variable {G:Gauge} {c f:Side} {S:StepData c f} {b:Clip} {D:PathData G} {χ:ChartRatio G}
  {I:Type} [Fintype I] [DecidableEq I] {R:Census I}
  (K:Bulk.Kernel S b D χ) (F:Forest S.ratio) (t:S.Choices)
  (W V:Bulk.Colors R G f) (w:W.Standard) (v:V.Standard) (x:fieldDir G c 1)
local notation "μ" => Gaussian.cloud (K.covariance F t)
local notation "draw" => Bulk.translated K F x

include w v in
omit [Fintype I] in
theorem standard_cubic (z:Bulk.Joint S F (G:=G)):
    jet (Bulk.geometric K F t W) 3 z=jet (Bulk.geometric K F t V) 3 z := by
  let E:=Bulk.geometric K F t V
  let h:=Bulk.supplement S F W-Bulk.supplement S F V
  have va:GradeAt 5 h:=(Bulk.joint_receipt S F w.2).sub (Bulk.joint_receipt S F v.2)
  have sm:ContDiffAt ℝ ω E 0:=(Bulk.stone_smooth K F t).add (Bulk.fee_starts K F V v.1).smooth
  have eq:Bulk.geometric K F t W=E+h:=by
    funext q
    change _+(_+Bulk.supplement S F W q)=(_+(_+Bulk.supplement S F V q))+(Bulk.supplement S F W q-Bulk.supplement S F V q)
    abel
  rw [eq,show jet (E+h) 3 z=jet E 3 z+jet h 3 z from by
    unfold Assembly.jet;rw [iteratedFDeriv_add_apply (sm.of_le le_top) (va.smooth.of_le le_top),_root_.add_apply,smul_add],va.jet_z z (by decide),add_zero]

def sourceFirst (z:Key F G→ℝ):Poly R:=lit R (fun i=>jet (Bulk.markFn S F W i) (W.power i+1) (draw z))
def sourceHead (z:Key F G→ℝ):Poly R:=(QuadraticLocal.Earn.Air.discharge W 0 (fineVelocity F (draw z)).2).pass

include w v
/-- Exact first-grade interacting comparison once the leading source jets agree
on this selected conditional draw. Its two Standard vacua may differ. -/
theorem physical_first_aligned (r:ℕ) (pos:0<r)
    (head:∀ z,sourceHead K F W x z=sourceHead K F V x z):
    First.ind (logMarked (Bulk.Fk K F t W x r))-First.ind (logMarked (Bulk.Fk K F t V x r))=
      wickEntries (K.covariance F t) (fun z=>(sourceFirst K F W x z-sourceFirst K F V x z)*sourceHead K F W x z) * inverseMass (gaussianLamp K F t W x) := by
  have lamp:gaussianLamp K F t W x=gaussianLamp K F t V x:=by
    ext1 m;apply integral_congr_ae;filter_upwards with z;exact congrArg (fun P:Poly R=>P.part m) (head z)
  have funprice (T:Bulk.Colors R G f) (hT:T.Standard) (m:R.Mode):
      Integrable (fun z=>(firstVertices K F t T x z*sourceHead K F T x z).part m) μ:=by
    have h:=(gather (r:=1) (Bulk.stage K F x) (Bulk.hinge F) T.power (Bulk.markFn S F T) (Bulk.geometric K F t T)
      (K.covariance F t) (K.symm F t) (K.positive F t) m (pick 1 1)).1
    rw [picked 1 (le_refl 1)] at h
    exact h.congr (.of_forall fun z=>physical_rows_first K F t T hT.1 x z m)
  have raw:firstMoment K F t W x-firstMoment K F t V x=wickEntries (K.covariance F t)
      (fun z=>(sourceFirst K F W x z-sourceFirst K F V x z)*sourceHead K F W x z):=by
    ext1 m
    change (∫ z,(firstVertices K F t W x z*sourceHead K F W x z).part m ∂μ)-
        (∫ z,(firstVertices K F t V x z*sourceHead K F V x z).part m ∂μ)=_
    rw [←integral_sub (funprice W w m) (funprice V v m)]
    apply integral_congr_ae;filter_upwards with z
    rw [←head z,←part_sub,←sub_mul]
    congr 2
    change (_+sourceFirst K F W x z)-(_+sourceFirst K F V x z)=_
    rw [standard_cubic K F t W V w v (draw z)];abel
  rw [physical_first_centered K F t W x w r pos,physical_first_centered K F t V x v r pos,←lamp]
  rw [sub_sub_sub_cancel_right,←sub_mul,raw]
end YM.Integration.FVA1Physical.Wilson
