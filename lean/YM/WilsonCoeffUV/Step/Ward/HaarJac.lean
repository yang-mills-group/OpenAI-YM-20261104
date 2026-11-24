import YM.WilsonCoeffUV.Step.Ward.Recenter
/-! Signed jacobian of the scaled, triangular coordinate change. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Power
open Lattice Laurent Bloch Exterior Wilson Precision RG Function Filter
open Blue MeasureTheory Set Metric Matrix Gauge
open FreeResolvent Tree
open YM.PertExtension.Chart (tangent physical expLinks jacobian fee)
open scoped ContDiff Topology BigOperators Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {c f : Side}{G:Gauge}(S:StepData c f)(F:Forest S.ratio)
variable {Y:Type}[Fintype Y][DecidableEq Y]
variable (M:Matrix (Woods G f) (Woods G c) ℝ) (X X': Lawn Y→ TreeVars G c)
omit [DecidableEq Y] in
lemma surface_det (v: Lawn (Active G F⊕Y))(H) (h:DifferentiableAt ℝ H (ride S F M X v)) (hd:DifferentiableAt ℝ (wend S F M X X' H) v) :
    (edgeM (wend S F M X X' H) v).det=(fderiv ℝ (fun y=>H (y,rightArm v)) (ride S F M X v).1).det := by
  rw [edge_det _ v hd]
  let C:=F.Free→G.Color; let k : C→C:=fun u=>H (u,rightArm v)
  let t:= vcloth S F G; let ξ:=fun z=> t (z+ rise S F M X (rightArm v))
  have he: ξ (leftArm v) = (ride S F M X v).1:=rfl
  have hξ (z): HasFDerivAt ξ t.toContinuousLinearMap z:= by
    have hη := t.hasFDerivAt.comp z ((hasFDerivAt_id (𝕜:=ℝ) z).add_const (rise S F M X (rightArm v)))
    simpa only [ContinuousLinearMap.comp_id] using! hη
  have ht: DifferentiableAt ℝ k (ξ (leftArm v)):= (show DifferentiableAt ℝ H ((fun y:C=> (y,rightArm v)) (ξ (leftArm v))) from h).comp (f:=fun y:C=>(y,rightArm v)) _ (differentiableAt_id.prodMk (differentiableAt_const _))
  have hx : (fun s=> wend S F M X X' H (Sum.elim s (rightArm v))) = fun s=> t.symm (k (ξ s)) - rise S F M X' (rightArm v) := rfl
  let d:= fderiv ℝ k (ξ (leftArm v)); let N:=t.symm.toContinuousLinearMap
  have hh: fderiv ℝ (fun s=> wend S F M X X' H (Sum.elim s (rightArm v))) (leftArm v)= N ∘L (d ∘L t.toContinuousLinearMap) := by rw [hx]; exact (((ContinuousLinearEquiv.hasFDerivAt t.symm).comp (leftArm v) (ht.hasFDerivAt.comp _ (hξ _))).sub_const _).fderiv
  rw [hh]; exact LinearMap.det_conj d.toLinearMap t.symm.toLinearEquiv

variable (s:Signed)(b:Site c)(q:Lawn Y→Site c→G.El)(Ñ:ChartRatio G)
local notation "Ξ"=> surf S F s b q
local notation "θ"=> wend S F M X X' (surf S F s b q)
def city (v:Lawn (Active G F ⊕ Woods G c)) := unhaar Ñ (camSlice G S F M*ᵥ v)

omit [DecidableEq Y] in
lemma city_area (A:TurnsG s b q X X')(p:LocalRatio Ñ)(he:M=reveal G S F*((reveal G S F).transpose*M)) :
     ∀ᶠ v:Lawn (Active G F ⊕ Y) in 𝓝 0, |(edgeM θ v).det| * Real.exp (city S F M Ñ (east S F M X X' Ξ v)) = Real.exp (city S F M Ñ (west S F X v)) := by
  have h₀:=surf_diff S F s b A; have hf:=surf_zero S F s b A
  have ht := areaP p Ξ hf (fun w=> retract S F s b (drifter S q w)) (fun w=> retract_pres ..) (fun w=>retract_inj S F s b _) h₀ (surf_auth S F s b A)
  have h := (ride_diff S F M X A.g₀).continuousAt.tendsto; rw [ride_zero _ _ _ _ A.f₀] at h
  have hw := h₀.continuousAt.tendsto; rw [hf] at hw
  have hs:= log_event S F p
  have hp:= wend_diff S F M X X' A.g₀ A.f₀ A.g₁ _ h₀
  filter_upwards [h.eventually ht, h.eventually (hw.eventually hs), h.eventually ((continuous_fst.tendsto _).eventually hs), hp.eventually (by simp),h.eventually (h₀.eventually (by simp))] with v hv hb hh ha hu
  rw [surface_det S F M X X' v _ (hu.differentiableAt (by simp)) (ha.differentiableAt (by simp)), city,city, west_log _ _ M X he v,east_log _ _ M X X' _ he v]
  apply mul_left_cancel₀ (a:=Ñ.scale^Fintype.card F.Free) (pow_ne_zero _ p.scale.ne')
  rw [mul_left_comm,hb,hh]; apply hv

-- absorb orientation into constant R det; tr is its sign (absolute determinant is one).
omit [DecidableEq Y] in
lemma arm_det (A:TurnsG s b q X X')(p:LocalRatio Ñ)(he:M=reveal G S F*((reveal G S F).transpose*M)) : |(edgeM θ 0).det|=1 := by
  have hv := mem_of_mem_nhds (city_area S F M X X' s b q Ñ A p he)
  change |(edgeM θ 0).det| * Real.exp _ = Real.exp _ at hv
  rw [east_zero _ _ M X X' A.f₀ A.f₁ _ (surf_zero _ _ s b A),west_zero _ _ _ A.f₀,city, Matrix.mulVec_zero,unhaar_zero p,Real.exp_zero,mul_one] at hv; exact hv
omit [DecidableEq Y] in
lemma det_jet (A:TurnsG s b q X X')(p:LocalRatio Ñ)(he:M=reveal G S F*((reveal G S F).transpose*M)) :
    jet (fun v=>|(edgeM θ v).det|) = realS ((edgeM θ 0).det) * (motionJ (spool θ)).det := by
  let Q:= θ
  have hθ : Green Q:= wend_diff S F M X X' A.g₀ A.f₀ A.g₁ _ (surf_diff S F s b A)
  have he' : Q 0=0 := wend_zero _ _ _ _ _ _ (surf_zero _ _ _ _ A) A.f₀ A.f₁
  have hm i j:= edge_green Q hθ i j; let d v := (edgeM Q v).det
  have hd : Green d:= by unfold d; simp_rw [det_apply']; apply ContDiffAt.sum; intro _ _; exact ContDiffAt.mul contDiffAt_const (contDiffAt_prod (fun i _=> hm _ i))
  have hb: |d 0|=1 := arm_det S F M X X' s b q Ñ A p he
  have hy: (fun v=> |d v|)=ᶠ[𝓝 0] (fun _=> d 0)*d := by
    rcases abs_eq_abs.mp (by rwa [abs_one]: |d 0|=|(1:ℝ)|) with e'|e'
    · filter_upwards [hd.continuousAt.eventually (lt_mem_nhds (show 0<d 0 by rw [e']; norm_num))] with i hi; change _=d 0*d i; rw [abs_of_pos hi,e',one_mul]
    filter_upwards [hd.continuousAt.eventually (gt_mem_nhds (show d 0<0 by rw [e']; norm_num))] with i hi; change _=d 0*d i; rw [abs_of_neg hi,e']; ring
  change jet (fun v=>|d v|)= _; rw [jet_congr hy,jet_mul contDiffAt_const hd,jet_const]; rw [show d=_ from rfl, solar_motion Q hθ he']
end YM.WilsonCoeffUV.Power
