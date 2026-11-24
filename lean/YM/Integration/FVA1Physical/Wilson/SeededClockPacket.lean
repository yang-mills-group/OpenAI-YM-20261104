import YM.Integration.FVA1Physical.Wilson.HomogeneousPainter
import YM.Integration.FVA1Physical.Wilson.FirstSourceWarp

/-! The independently computed finite conditional connected log, after the
actual physical change of clock, is realized as one joint analytic input
germ on the next forest. This pointwise chart prescription keeps its two
clock contributions distinct and refers back to the original conditional
kernel and denominator. -/
set_option autoImplicit false
set_option maxHeartbeats 2100000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter Finset Lattice RG Exterior Tree Precision Marker Multi
open YM.Wilson QuadraticLocal.Sunrise Comparison.RG02 Assembly Valence Adjacent
open scoped Topology Classical ContDiff BigOperators
variable {G:Gauge} {I:Type} [Fintype I] [DecidableEq I] {R:Census I}
  {c f:Side} {S:StepData c f} {p:Clip} {P:PathData G} {O:ChartRatio G}
  (K:Bulk.Kernel S p P O) (F:Forest S.ratio) (tag:S.Choices) (C:Bulk.Colors R G f) (η:I→ℕ)
  (s:Hot R) (r:ℕ) (cost:UnitCost)

def loopReset (j:ℕ) (x:fieldDir G c 1):ℂ:=
  born (fun l y=>(Order.observe R r (Order.logMarked (Bulk.Fk K F tag C (Stationary.arm G c 1 y) r)) l).part s.val)
    cost 0 r j ((Stationary.arm G c 1).symm x)

theorem loopReset_degree (valid:∀a:Hot R,C.power a=Launch.index R η a.val+1) (j:ℕ) (hj:j≤r):
    Level ((Launch.index R η s.val+1+j:ℕ):ℤ) (loopReset K F tag C s r cost j) := by
  have base:=mixed_engineering_reset K F tag C η valid s r j hj cost 0
  have h:=SignCovariance.affine_degree 0 (Stationary.arm G c 1).symm.toContinuousLinearMap base
  unfold loopReset
  simp only [zero_add] at h
  exact h

def forestLog (V:Config G c):fieldDir G c 1:=fun i=>G.plog (G.mat (V (i.1,axisEquiv.symm i.2)))

private theorem forestLog_retract :
    ∀ᶠ x:fieldDir G c 1 in 𝓝 0, forestLog (represent x)=x := by
  have single (e:Body 1 c):∀ᶠ x:fieldDir G c 1 in 𝓝 0,G.plog (G.mat (G.lieExp (x e)))=x e:=by
    have pr:Tendsto (fun x:fieldDir G c 1=>x e) (𝓝 0) (𝓝 0):=(continuous_apply e).tendsto (0:fieldDir G c 1)
    exact pr.eventually G.plog_left
  filter_upwards [Filter.eventually_all.mpr single] with x hx
  funext e
  simpa only [forestLog,Work.F03.represent_link,show coord (axisEquiv.symm e.2)=e.2 from axisEquiv.apply_symm_apply _] using hx e

def germPainter (t:ℝ) (V:Config G c):ℂ:=clockPacket (Launch.index R η s.val+1) r
  (loopReset K F tag C s r cost) (t,forestLog V)

theorem germPainter_chart : Bulk.projected (germPainter K F tag C η s r cost)=ᶠ[𝓝 0]
      clockPacket (Launch.index R η s.val+1) r (loopReset K F tag C s r cost) :=by
  filter_upwards [continuous_snd.continuousAt.tendsto.eventually (forestLog_retract (G:=G) (c:=c))] with v hv
  change clockPacket _ _ _ (v.1,forestLog (represent v.2))=_
  rw [hv]

theorem germPainter_read (valid:∀a:Hot R,C.power a=Launch.index R η a.val+1)
    (j:ℕ) (hj:j≤r) (x:fieldDir G c 1):
    jet (Bulk.projected (germPainter K F tag C η s r cost)) (Launch.index R η s.val+1+j) (1,x) =
      loopReset K F tag C s r cost j x := by
  have eq:=germPainter_chart K F tag C η s r cost
  calc _ = jet (clockPacket (Launch.index R η s.val+1) r (loopReset K F tag C s r cost)) _ (1,x) := by
         unfold Assembly.jet;rw [(eq.iteratedFDeriv ℝ _).eq_of_nhds]
       _ = _ := clockPacket_read (fun j hj=>loopReset_degree K F tag C η s r cost valid j hj) hj x

end YM.Integration.FVA1Physical.Wilson
