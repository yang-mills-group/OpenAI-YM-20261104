import YM.WilsonCoeffUV.Step.Rotation.Germ
/-!
# Recenter between the means belonging to each tree.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Power.Freedom
open Wilson Lattice Laurent Exterior Bloch Matrix Precision Stationary RG Blue
open Next.Free FreeResolvent Tree Work.F05 Function Filter Gauge
open YM.PertExtension.Chart (expLinks jacobian physical)
open MeasureTheory
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {c f : Side}{G:Gauge}(S:StepData c f)
variable {B T:Forest S.ratio}(e:B.Free≃T.Free)
variable (M M' : Matrix (Woods G f) (Woods G c) ℝ)

-- subtract already imposed means in the target
private def tide (v:Sector (S:=S) (G:=G) (B:=B)) := vcloth S B G (rise S B M id v.2) - (Work.F05.index e).symm (vcloth S T G (rise S T M' id v.2))
def notch := fresh (G:=G) S e + tide S e M M'
lemma notch_lit (v): notch S e M M' v=fresh S e v+(vcloth S B G (rise S B M id v.2) -(Work.F05.index e).symm (vcloth S T G (rise S T M' id v.2))):= rfl
lemma notch_green : ContDiffAt ℝ ω (notch S e M M') 0 := by
  let Γ:= Sector (S:=S) (G:=G) (B:=B)
  have he (N:Matrix (Woods G f) (Woods G c) ℝ)(F:Forest S.ratio) : ContDiff ℝ ω (fun v:Γ=> vcloth S F G (rise S F N id v.2)) := (vcloth S F G).contDiff.comp ((((reveal G S F).transpose*N).mulVecLin.toContinuousLinearMap.contDiff).comp (f:=Prod.snd) contDiff_snd)
  exact (fresh_green S e).add ((he M B).contDiffAt.sub (((Work.F05.index e).symm.contDiff.comp (f:=fun v:Γ=> vcloth S T G (rise S T M' id v.2)) (he M' T)).contDiffAt))
lemma notch_zero : notch S e M M' 0=0 := by rw [notch_lit, fresh_zero]; simp [rise]

def beam := bridgeM (stripe S e (G:=G)) (Woods G c)
def spoke := east S B M id id (notch S e M M')
def internal := wend S B M id id (notch S e M M')
def pan (v:Lawn (Active G B⊕Woods G c)) := beam S e *ᵥ spoke S e M M' v
private abbrev hub := Lawn (Active G B⊕ Woods G c)
lemma pan_join (u):
    leftArm (pan S e M M' u)=stripe S e *ᵥ internal S e M M' u ∧ rightArm (pan S e M M' u)=rightArm u := bridgeArms ..
lemma pan_H (u:hub (S:=S) (G:=G) (B:=B)) (he:M'=reveal G S T*((reveal G S T).transpose*M')) :
    let Φ:= fresh S e (ride S B M id u)
    camSlice G S T M' *ᵥ pan S e M M' u = reveal G S T *ᵥ (vcloth S T G).symm (Work.F05.index e Φ) := by
  intro Φ
  have hy : vcloth S T G (stripe S e *ᵥ internal S e M M' u)= Work.F05.index e Φ - vcloth S T G (rise S T M' id (rightArm u)) := by
    rw [v_exchange,internal,wend,map_sub,ContinuousLinearEquiv.apply_symm_apply, notch_lit]
    have h : (ride S B M id u).2=rightArm u :=rfl
    rw [h,map_sub,map_add,map_sub,ContinuousLinearEquiv.apply_symm_apply]; unfold Φ; abel
  have hV: M' *ᵥ rightArm u = reveal G S T *ᵥ rise S T M' id (rightArm u) := by rw [rise,Matrix.mulVec_mulVec,←he]; rfl
  rw [camber_tree,Matrix.add_mulVec, ← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,left_hit,right_hit,(pan_join S e M M' u).1,(pan_join S e M M' u).2,hV, ←Matrix.mulVec_add]; congr 1
  apply (vcloth S T G).injective; rw [map_add, hy, sub_add_cancel, ContinuousLinearEquiv.apply_symm_apply]
lemma outset (he:M=reveal G S B * ((reveal G S B).transpose*M))(u:hub (S:=S) (G:=G) (B:=B)) :
    camSlice G S B M *ᵥ u= reveal G S B *ᵥ (vcloth S B G).symm (ride S B M id u).1 := by
  have hh : west S B id u=u:= funext fun i=>by cases i<;> rfl
  simpa only [hh] using west_log S B M id he u
lemma spoke_zero : spoke S e M M' 0=0:= east_zero S B M id id rfl rfl _ (notch_zero ..)
lemma internal_zero : internal S e M M' 0=0:= wend_zero S B M id id _ (notch_zero ..) rfl rfl
lemma internal_green : Green (internal S e M M'):= wend_diff S B M id id contDiffAt_id rfl contDiffAt_id _ (notch_green ..)
lemma spoke_green : Green (spoke S e M M'):= east_diff S B M id id contDiffAt_id rfl contDiffAt_id _ (notch_green ..)
lemma expose_zero : pan S e M M' 0=0:= by rw [pan,spoke_zero,Matrix.mulVec_zero]
private lemma as_board {U V W:Type}[Fintype U][Fintype V][Fintype W](P : Matrix U V ℝ){F:Lawn W→Lawn V} (h:Green F)(e:F 0=0) : Green fun v=> P*ᵥ F v := by
  classical
  exact (show ContDiffAt ℝ ω (fun v=>P *ᵥ v) (F 0) from e.symm ▸ board P).comp 0 h
lemma expose_green : Green (pan S e M M') := as_board _ (spoke_green ..) (spoke_zero ..)

-- Checking the shift under arbitrary rooted model gauges
variable (T) in
def localPhi (u:hub (S:=S) (G:=G) (B:=B)) := T.foldAt (rawD S B (ride S B M id u))
lemma localPhi_green (T:Forest S.ratio) (i:Site f) : Green fun u=>G.mat (localPhi S (B:=B) T M u i) := by
  let H := gauge_green (G:=G) S (B:=B) T i
  rw [← ride_zero S B M id rfl] at H
  exact H.comp (f:=ride S B M id) _ (ride_diff S B M id contDiffAt_id)
lemma pan_turn (hB:M=reveal G S B*((reveal G S B).transpose*M))(hT:M'=reveal G S T*((reveal G S T).transpose*M')) :
    TurnsG 1 0 (localPhi S T M) (fun u=>camSlice G S B M*ᵥ u) (fun u=> camSlice G S T M'*ᵥ pan S e M M' u) := by
  have hx: Tendsto (ride S B M id) (𝓝 0) (𝓝 0) := ride_zero _ _ _ id rfl ▸ (ride_diff _ _ _ id contDiffAt_id).continuousAt
  refine ⟨board _,as_board _ (expose_green ..) (expose_zero ..),Matrix.mulVec_zero _,by rw [expose_zero,Matrix.mulVec_zero],fun i=> localPhi_green ..,?_⟩
  filter_upwards [hx.eventually (fresh_auth S e)] with u hu
  let r:=ride S B M id u
  have he : expLinks G T.Free (Work.F05.index e (fresh S e r))=collapse S T (rawD S B r) := by
    apply (shiftPi G S e).injective
    rw [← newG_at, re_expose]; exact hu
  rw [pan_H S e M M' u hT,outset S M hB,v_extend,v_extend,ContinuousLinearEquiv.apply_symm_apply,ContinuousLinearEquiv.apply_symm_apply,he,pull_id,tree_coll]; rfl
end YM.WilsonCoeffUV.Power.Freedom
