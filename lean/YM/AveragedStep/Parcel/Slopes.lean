import YM.AveragedStep.Parcel.Retain
/-! score calculations (x = exponential log, UNSCALED). Extend slope to
entire local vector space boundedly before using the reader. -/
set_option autoImplicit false
noncomputable section
namespace YM.AveragedStep
open Filter Function Lattice RG Loops Tree Wilson Precision Metric Set MeasureTheory
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical
variable {G:Gauge}{P:Patch}{K:KernelChoices}{A:ChartRatio G}(Q:Cuff P K A)

def bandD(a:Mold)(v:Vectors P G):Vectors P G →L[ℝ] ℝ:=
  if ‖v‖ ≤ 2*Q.width then fderiv ℝ (chip P K a (canon P)) v else 0
lemma band_env (a:Mold): Envelope (bandD Q a):=by
 let F:=fderiv ℝ (chip P K a (canon P) (G:=G)); let s:=closedBall (0:Vectors P G) (2*Q.width)
 have hf:ContinuousOn F s:=by
    intro x hx; apply ContinuousAt.continuousWithinAt
    have he:‖x‖≤ 3*Q.width:= by unfold s at hx; rw [mem_closedBall,dist_zero_right] at hx; linarith [Q.active]
    exact ((Q.analytic a x he).fderiv_right (m:=ω) (by simp)).continuousAt
 obtain ⟨C,hC⟩:= isCompact_closedBall (0:Vectors P G) (2*Q.width) |>.exists_bound_of_continuousOn hf
 have he:bandD Q a= s.piecewise F (0:Vectors P G→ _) := by funext i; simp only [s,piecewise,mem_closedBall_zero_iff]; rfl
 refine ⟨he ▸ hf.measurable_piecewise continuous_const.continuousOn measurableSet_closedBall,max C 0,fun v=>?_⟩ -- rw
 unfold bandD; split
 next h=> exact (hC _ (show v∈s from by rwa [show s=_ from rfl,mem_closedBall_zero_iff])).trans (le_max_left ..)
 rw [norm_zero]; exact le_max_right ..
lemma band_applied (a:Mold)(v:Vectors P G): Envelope (fun i=>bandD Q a i v):=by
 obtain ⟨D,H⟩:= (band_env Q a).cost
 exact ⟨((show Continuous (fun F:Vectors P G→L[ℝ]ℝ=> F v) from continuous_id.clm_apply continuous_const).measurable.comp (band_env Q a).meas),D*‖v‖,fun i=>(ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (H _) (norm_nonneg _))⟩
include Q
lemma log_j_env (L:LocalRatio A) (v:G.Color) : Envelope (fun g:G.El=> Cuff.haarScore (A:=A) (Q.logC g) v):=by
  let s:= closedBall (0:G.Color) (2*Q.width)
  let F(u:G.Color):=Cuff.haarScore (A:=A) u v
  have he:ContinuousOn F s:=by
    intro x hx; apply ContinuousAt.continuousWithinAt
    have h:x∈ball 0 A.radius:= Q.withinH hx
    exact ((((L.germ x h).fderiv_right (m:=ω) (by simp)).continuousAt.clm_apply continuousAt_const).div (L.germ x h).continuousAt (L.pos x h).ne')
  have hq : Measurable (s.piecewise F 0):=he.measurable_piecewise continuous_const.continuousOn measurableSet_closedBall
  obtain ⟨B,H⟩:= isCompact_closedBall (0:G.Color) (2*Q.width) |>.exists_bound_of_continuousOn he
  have hz(g):Q.logC g∈s:=by change Q.logC g∈closedBall 0 (2*Q.width); rw [mem_closedBall_zero_iff]; exact Q.log_max g
  refine ⟨?_ ,B,fun g=>H _ (hz _)⟩
  convert! hq.comp Q.log_meas using 1; exact (show _ from (funext (fun g=>by unfold Function.comp; rw [piecewise_eq_of_mem s F _ (hz g)])).symm)

omit Q
variable {c f:Side}{S:StepData c f} (F:Forest S.ratio)
variable {Q} (C:Cuff S.patch S.kernel A)
-- linear forms in fields (NO curve reexpansion implicit)
private def castQ (p:Parcel c f):(Rim c f→ G.Color) →L[ℝ] Vectors S.patch G:=
  LinearMap.toContinuousLinearMap
    ({toFun:=pick (S:=S) p
      map_add':=by intro x y; funext i; unfold pick; cases he:hook S p i <;> simp [Option.elim,he]
      map_smul':=by intro x y; funext i; unfold pick; cases he:hook S p i <;> simp [Option.elim,he]} : (Rim c f→ G.Color) →ₗ[ℝ] Vectors S.patch G)

def flame (e:Rim c f)(Z:Rim c f→G.Color)(v:G.Color) :=
    ∑ p∈owners S e, bandD C (sort p) (pick (S:=S) p Z) (pick (S:=S) p (Pi.single e v))
lemma flame_env (e v): Envelope (fun Z=>flame C e Z v):= Envelope.sum (owners S e) _
    (fun p=> env_comp (band_applied C (sort p) _) (g:=castQ (G:=G) (S:=S) p) (castQ p).continuous.measurable)
private def vary (Z:Rim c f→G.Color)(e:Rim c f)(v:G.Color): Rim c f→G.Color:=update Z e v
def introAt (e:Rim c f): G.Color →L[ℝ] (Rim c f→G.Color):=
    LinearMap.toContinuousLinearMap (LinearMap.single ℝ (fun _:Rim c f=> G.Color) e)
lemma intro_eq (e:Rim c f)(w:G.Color):introAt e w=Pi.single e w:=rfl
lemma sends (Z:Rim c f→G.Color)(e)(x:G.Color):
    HasFDerivAt (fun z=>update Z e z) (introAt e) x:=by
 have he : (fun z:G.Color=>update Z e z)=(fun z=>(update Z e 0)+introAt e z):=by funext v i; by_cases h:i=e <;> simp [h,intro_eq]
 rw [he]; exact (introAt e).hasFDerivAt.const_add _
lemma close_deriv (Z:Rim c f→ G.Color)(e)(w:G.Color)(h:∀ z∈home S e,‖(update Z e w) z‖≤2*C.width):
    ContDiffAt ℝ ω (fun v=>close (S:=S) e (update Z e v)) w ∧
    ∀ i:G.Color,fderiv ℝ (fun v=>close (S:=S) e (update Z e v)) w i=flame C e (update Z e w) i:=by
  let X:=update Z e w
  have hz:ContDiff ℝ ω (fun v:G.Color=>update Z e v):=contDiff_pi.mpr fun i=> by
     by_cases h:i=e; · subst i; simp; exact contDiff_id
     simp_rw [update_of_ne h]; exact contDiff_const
  have hp(p:Parcel c f)(hp:p∈owners S e): ‖pick (S:=S) p X‖≤2*C.width:=by
    refine (pi_norm_le_iff_of_nonneg (by have :=C.active; positivity)).mpr fun i=>?_; unfold pick; cases he:hook S p i; · simp only [Option.elim, norm_zero]; have ht:=C.active; positivity
    next i=> exact h i (home_owner S hp (land_mem S he))
  have hv(p)(ht:p∈owners S e):= C.analytic (sort p) _ ((hp p ht).trans (show 2*C.width≤3*C.width from by linarith [C.active]))
  let g(p:Parcel c f):=fun v:G.Color=> pick (S:=S) p (update Z e v)
  let F(p:Parcel c f):=chip S.patch S.kernel (sort p) (canon S.patch) (G:=G)
  have ht(p:Parcel c f)(hh:p∈owners S e):ContDiffAt ℝ ω (fun v=>F p (g p v)) w:=
     ContDiffAt.comp (f:=g p) w (hv p hh) ((castQ p).contDiff.comp hz).contDiffAt
  dsimp only [close]
  constructor
  · exact ContDiffAt.sum ht
  intro i; have hj:=HasFDerivAt.fun_sum (u:=owners S e) (fun p hh => ((hv p hh).differentiableAt (by simp)).hasFDerivAt.comp w
      ((castQ (G:=G) p).hasFDerivAt.comp (f:=fun v=>update Z e v) w (sends Z e w)))
  have he:=congr_arg (fun L:G.Color→L[ℝ] (ℝ)=>L i) hj.fderiv
  -- align sums
  unfold flame; change fderiv ℝ _ _ _ = ∑ p ∈ owners S e,_
  rw [show fderiv ℝ (fun (v:G.Color)=> ∑ p∈owners S e,F p (g p v)) w i = _ from he]
  simp_rw [sum_apply,ContinuousLinearMap.comp_apply,intro_eq]; refine Finset.sum_congr rfl fun p hh=>?_; unfold bandD; rw [if_pos (hp p hh)]; rfl
end YM.AveragedStep
