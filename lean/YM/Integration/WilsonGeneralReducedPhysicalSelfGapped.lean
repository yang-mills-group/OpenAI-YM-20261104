import YM.Integration.WilsonGeneralReducedPhysicalSelfBoard

/-! A smooth uncentered, same-field norming test within the genuine reflected
Born margin whose two compact placements also have a gap on every axis. -/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonGeneralReducedPhysicalSelfGapped
open Set Filter Metric Lattice Maxwell MS MS.Menus Local.Physical Extra Extra.FD
open Table.Pairing XSpace XSpace.Cirrus XSpace.Rose XSpace.Normalize
open WilsonPositionProgramPublicReflectedRead (lower placement)
open WilsonPositionProgramPublicWickGram (vertex)
open scoped Topology Classical
def rise:Points 2:=points (fun i=>if i=0 then 0 else WithLp.toLp 2 (fun _:Axis=>(1:ℝ)))
def pose (a:Axis)(t:ℝ):Points 2:=lower a+t • rise

theorem aperture (a:Axis)(t:ℝ)(i:Axis):
    pose a t 1 i-pose a t 0 i=t+(if i=a then 1 else 0):=by
  rw [pose,placement]
  by_cases eq:i=a <;> simp [rise,FD.couple,vertex,YM.basis,eq] <;> ring

theorem original (a:Axis){r:ℝ}(rp:0<r):
    ∃(p:Points 2)(B:ContDiffBump p)(σ:ℝ),0<σ ∧
      ∀y∈tsupport B,dist y (lower a)<r ∧ ∀i:Axis,σ<y 1 i-y 0 i:=by
  have drift:ContinuousAt (pose a) 0:=by unfold pose;fun_prop
  have close:∀ᶠ t in 𝓝 (0:ℝ),dist (pose a t) (lower a)<r:=by
    have law:=drift.tendsto.eventually (Metric.ball_mem_nhds _ rp)
    simpa only [pose,zero_smul,add_zero,Metric.mem_ball] using law
  have both:∀ᶠ t:ℝ in 𝓝[>] 0,0<t ∧ dist (pose a t) (lower a)<r:=
    (show ∀ᶠ t:ℝ in 𝓝[>] 0,0<t from self_mem_nhdsWithin).and (close.filter_mono nhdsWithin_le_nhds)
  obtain ⟨t,tp,near⟩:=both.exists
  let p:=pose a t
  have good:∀i:Axis,∀ᶠ y:Points 2 in 𝓝 p,t/2<y 1 i-y 0 i:=by
    intro i
    have positive:t/2<p 1 i-p 0 i:=by
      rw [show p=pose a t from rfl,aperture]
      split <;>linarith
    exact (show Continuous (fun y:Points 2=>y 1 i-y 0 i) from by fun_prop).continuousAt.preimage_mem_nhds
      (lt_mem_nhds positive)
  have distNear:∀ᶠ y:Points 2 in 𝓝 p,dist y (lower a)<r:=
    (show Continuous (fun y:Points 2=>dist y (lower a)) from by fun_prop).continuousAt.preimage_mem_nhds (gt_mem_nhds near)
  have within:{y:Points 2|dist y (lower a)<r ∧ ∀i:Axis,t/2<y 1 i-y 0 i}∈𝓝 p:=
    distNear.and (Filter.eventually_all.mpr good)
  obtain ⟨b,bp,sub⟩:=Metric.mem_nhds_iff.mp within
  let B:ContDiffBump p:=⟨b/4,b/2,by linarith,by linarith⟩
  refine ⟨p,B,t/2,half_pos tp,?_⟩
  intro y hy
  rw [B.tsupport_eq] at hy
  exact sub (Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hy).trans_lt (by change b/2<b;linarith)))

end YM.Integration.WilsonGeneralReducedPhysicalSelfGapped
