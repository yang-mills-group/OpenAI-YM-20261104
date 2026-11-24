import YM.Integration.WilsonGeneralReducedPhysicalSelfGappedSmooth
import YM.Integration.WilsonMeasuredPublicEntranceActionGram
/-! A fixed smooth, separated pair can hear the nonvanishing reflected
ground of the signed original action. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 450000
noncomputable section
namespace YM.Integration.WilsonMeasuredSignedActionSmoothPacket
open Function Filter Set Spec Table Climb Trace Trace.Pilot PhysMS Maxwell Maxwell.Free
open XSpace XSpace.Normalize Next.Rank OPE OPE.Orbits
open TopologicalSpace MeasureTheory PertExtension.Rigidity.Positive
open WilsonPhysicalPositionReflectedReturn (sites clear)
open scoped Topology Classical BigOperators ComplexOrder
open private integrated from YM.Integration.WilsonGeneralReducedPhysicalSelfGappedSmooth

theorem detects {x:Points 2}(clear:x∈conf 2)(f:Points 2→ℂ)(smooth:ContinuousOn f (conf 2))
    (alive:f x≠0):∃b:ContDiffBump x,tsupport b⊆conf 2 ∧ (∫y:Points 2,b.normed volume y • f y)≠0:=by
  let tol:=‖f x‖/2
  have pos:0<tol:=half_pos (norm_pos_iff.mpr alive)
  have contAt:ContinuousAt f x:=(smooth x clear).continuousAt ((conf_open _).mem_nhds clear)
  have win:{y:Points 2|y∈conf 2 ∧ ‖f y-f x‖<tol}∈𝓝 x:=by
    have cont:=contAt.tendsto.eventually (Metric.ball_mem_nhds (f x) pos)
    have near:∀ᶠ y in 𝓝 x,y∈conf 2:=(conf_open _).mem_nhds clear
    have close:∀ᶠ y in 𝓝 x,‖f y-f x‖<tol:=by simpa only [Metric.mem_ball,dist_eq_norm] using cont
    exact near.and close
  obtain ⟨r,rp,room⟩:=Metric.mem_nhds_iff.mp win
  let b:ContDiffBump x:=⟨r/4,r/2,by linarith,by linarith⟩
  have space(y:Points 2)(live:y∈tsupport b):y∈conf 2 ∧ ‖f y-f x‖<tol:=by
    rw [b.tsupport_eq] at live
    exact room (Metric.mem_ball.mpr ((Metric.mem_closedBall.mp live).trans_lt (by change r/2<r;linarith)))
  let f₀:Points 2→ℂ:=(conf 2).piecewise f (fun _=>0)
  have meas:Measurable f₀:=smooth.measurable_piecewise continuous_zero.continuousOn (conf_open _).measurableSet
  have sold(y:Points 2)(live:b.normed volume y≠0):y∈tsupport b:=by
    rw [b.tsupport_eq]
    apply Metric.ball_subset_closedBall
    rwa [←b.support_normed_eq (μ:=volume)]
  have same(y:Points 2)(live:b.normed volume y≠0):f₀ y=f y:=piecewise_eq_of_mem _ _ _ (space y (sold y live)).1
  have bound:=integrated b f₀ (fun _=>f x) meas measurable_const (C:=‖f x‖) (δ:=tol)
    (fun _ _=>le_refl _) (fun y alive=>by rw [same y alive];exact (space y (sold y alive)).2.le)
  rw [b.integral_normed_smul] at bound
  have agree:(∫y:Points 2,b.normed volume y • f y)=(∫y:Points 2,b.normed volume y • f₀ y):=by
    apply integral_congr_ae
    apply ae_of_all
    intro y
    by_cases eq:b.normed volume y=0
    · simp only [eq,zero_smul]
    · change b.normed volume y • f y=b.normed volume y • f₀ y
      rw [same y eq]
  refine ⟨b,fun y live=>(space y live).1,?_⟩
  intro zero
  rw [←agree,zero,zero_sub,norm_neg] at bound
  dsimp [tol] at bound
  linarith [norm_pos_iff.mpr alive]

variable {G:Gauge}(C:Family G)
local notation "M" => Bel C.book
local notation "F₄" => (Bel C.book).Field 4

def reflected (w:F₄):Points 2→ℂ:=
  WickGoal (C:=C) (d:=fun _:Fin 2=>4) ![w,(Bel C.book).adj (spin_free C.labels) 4 0 w]

def reading (b:ContDiffBump sites)(w:F₄):ℂ:=∫y:Points 2,b.normed volume y • reflected C w y

theorem ground (w:F₄):reflected C w sites=gramC C.labels (hierarchy C.labels) 0 w w:=by
  symm
  rw [gramC_apply]
  change (Bel C.book).useAt M sites _=(Bel C.book).useAt M sites (fun i:Fin 2=>(⟨4,(![w,(Bel C.book).adj (spin_free C.labels) 4 0 w]:Fin 2→F₄) i⟩:(Bel C.book).Tag))
  apply congrArg ((Bel C.book).useAt M sites)
  funext i
  fin_cases i <;>rfl

theorem original (simple:G.Simple)(H:(Bel C.book).Hierarchy):
    ∃b:ContDiffBump sites,tsupport b⊆conf 2 ∧ reading C b (stepField C)≠0:=by
  have alive:=scale_alive simple H
  apply detects clear (reflected C (stepField C))
    (fun q h=>(WickGoal_tied _ h).continuousAt.continuousWithinAt)
  rw [ground]
  exact ne_of_gt (gramC_pos C.labels (hierarchy C.labels) 0 alive)

end YM.Integration.WilsonMeasuredSignedActionSmoothPacket
end
