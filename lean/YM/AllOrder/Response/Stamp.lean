import YM.AllOrder.Response.Equip
/-!
# Full cylinder valuation in **unscaled** stationary frame & flat coefficients
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Response
open Finset Filter Function Laplace.SigmaP Laplace PositionX.Jet PertExtension PertExtension.Series PositionX.Gauss Radial Asymptotics MeasureTheory
open scoped Topology ContDiff BigOperators Classical
open GaussianScore
variable {Y X:Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup X][NormedSpace ℝ X] [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y]
    [MeasurableSpace Y][BorelSpace Y]{V:X×Y→ℝ}{ρ:X→Y}{A H:ℝ×(X×Y)→ℝ}(h:Treaty V ρ A H)
local notation "F"=> fderiv ℝ ρ 0
local notation "Ω"=> X×Y
set_option quotPrecheck false
local notation "Γ"=> castle V ρ h.steer
lemma castle_pays (y:Y): (castle V ρ h.steer).kern y= Real.exp (-vert V y):=by rw [Law.kern,vert,Laplace.curvature,jet_two_H]; apply congr_arg Real.exp; change -(fderiv ℝ (fderiv ℝ V) 0) (0,y) (0,y)/2=_; ring
variable (Γ':Law Y)(μ:Measure Y)[μ.IsAddHaarMeasure]
def climate (Γ':Law Y)(μ:Measure Y)(T:Book (X×Y)):Book X:=cloud Γ' μ (EXP T)
def connected (Γ':Law Y)(μ:Measure Y)(T:Book (X×Y)):Book X:=LOG (climate Γ' μ T)
local notation "S"=>Impulse F A H
variable {P:ℝ→X} (hp:ContDiffAt ℝ ω P 0) {r:ℝ}
def trust (P:ℝ→X)(M:X→L[ℝ] Y):= M ∘ echo P
local notation "Y₀"=> trust P (fderiv ℝ ρ 0)
def forecast (V:X×Y→ℝ)(P:ℝ→X)(M:X→L[ℝ] Y):= liftQ V M ∘ P
local notation "XX"=> liftQ V F
local notation "T"=> (H ∘ tone (echo P) Y₀)
local notation "W"=> prepare A (echo P) Y₀ r
local notation "Π"=> -forecast V P F
include hp h
omit h in
lemma lends : NextTo (ρ) (echo P) (trust P (fderiv ℝ ρ 0)) := by
   let V:= echo P; have he: V 0=0:= zero_smul ..; have hf: ContDiffAt ℝ ω V 0:= contDiffAt_id.smul hp
   refine ⟨he,hf, (congr_arg (⇑(fderiv ℝ ρ 0)) he).trans (map_zero _),(F).contDiff.contDiffAt.comp _ hf,fun x=>?_⟩; unfold trust; rw [fderiv_comp _ ((F).differentiableAt) (hf.differentiableAt (by simp)),ContinuousLinearMap.fderiv]; rfl
lemma smooth_top : ContDiffAt ℝ ω (Π) 0:= ((lift_cost V F).smooth.contDiffAt.comp (f:=P) _ hp).neg
variable (he:0<H 0)
include he
lemma approves (z:Y) : let T':= weigh (fun i=>(P i,z)); let A':= tilted P F A H z; let L:=H 0 * (Γ).kern z; someJ (Real.exp ∘ A')= L • plus (someJ (Real.exp ∘ (Π))) (T' (EXP S)):=by
   intro g a L; obtain ⟨ht,hC,H'⟩:= tilt_bill h hp z he; let hδ:0<L:= mul_pos he (Real.exp_pos _); let J (t:ℝ):= (Π) t +Real.log L -- parse
   have hg:ContDiffAt ℝ ω J 0:=(smooth_top h hp).add contDiffAt_const
   have hI:token F A H 0 ∘ (fun i=>(P i,z))=J:=by
      funext i; rw [comp_apply, projected h]; unfold J L; rw [Real.log_mul he.ne' (show (Γ).kern z≠0 from (Real.exp_pos _).ne'), castle_pays h z,Real.log_exp]; change _= -(XX (P i))+_; ring
   have hv: someJ a=g S+someJ J:=by
      funext i; rw [(show someJ a=_ from hC),← hI];
      let f:=token F A H; let Q:= fun i=>(P i,z)
      have hc:ContDiffAt ℝ ω Q 0:=hp.prodMk contDiffAt_const
      change _ = weigh Q (f-wirings (f 0)) i + _
      rw [weigh_sub hc (u:=f) (fun j _=> (token_cost F A H j).smooth.contDiffAt) (le_refl i) (install_just _ (token_cost F A H 0).smooth.contDiffAt), just_read hc (token_cost F A H 0).smooth.contDiffAt]; exact (sub_add_cancel _ _).symm
   rw [conviction ht, hv, add_comm (g S), exp_add, ← conviction hg]; unfold g; rw [show Real.exp ∘ J= (fun (_:ℝ)=> L)*(Real.exp ∘ Π) from funext (fun i=> by rw [comp_apply, show J i= (Π) i+Real.log L from rfl, Real.exp_add, Real.exp_log hδ]; exact mul_comm ..),some_mul contDiffAt_const (show ContDiffAt ℝ ω (Real.exp ∘ Π) 0 from Real.contDiff_exp.contDiffAt.comp _ (smooth_top h hp)), show someJ _=just L from funext fun i=> (Act.static L (n:=i)).writes _ le_rfl, exact_scale,show expS (weigh (fun i=>(P i,z)) S)=_ from funext fun i=> (weigh_exp (hp.prodMk contDiffAt_const) (u:=S) (fun j _=>(impulse_cost ..).smooth.contDiffAt) (win0 _) (le_refl i)).symm ]
   funext i; simp only [plus_sum, Pi.smul_apply,smul_eq_mul,mul_assoc, Finset.mul_sum]
-- biomechn
variable (hr: 0<Laplace.curvature V (fderiv ℝ (echo P) 0 1) (fderiv ℝ (trust P (fderiv ℝ ρ 0)) 0 1)+r)
include hr
lemma quoteP (y:Y): (fun n=> normTerm T W n (onLane y))= (Real.exp (-r)* (H 0 * (Γ).kern y)) • plus (someJ (Real.exp ∘ Π)) (weigh (fun t=>(P t,y)) (EXP S)) := by
   let L t:=(Real.exp (tilted P F A H y t)* Real.exp (-r)); have hv:= lends hp (ρ:=ρ); have hδ:= approved h hv hr; obtain ⟨hX,hΞ,hη⟩:= tilt_bill h hp y he; let f t:= colorful F (P t,y); let g (t:ℝ):=echo f t
   rw [coined («F»:=W) (g:= L) hδ.revenue hδ.income (by exact hX.exp.mul contDiffAt_const)]; swap
   · have hh : Tendsto (fun t=> H (g t)) (𝓝 0) (𝓝 (H 0)):= h.ample.continuousAt.tendsto.comp (show Tendsto g (𝓝 0) (𝓝 0) from (zero_smul ℝ (f 0)) ▸ (show ContinuousAt g 0 from (by unfold g f echo colorful; fun_prop (disch:=exact hp.continuousAt)))) -- need g0 rewrite
     filter_upwards [(hh.eventually (lt_mem_nhds he)).filter_mono nhdsWithin_le_nhds,hη,Tested.eventually_pos] with t ht h' ht₀
     have hF : tone (echo P) Y₀ (t • onLane y)=g t:= by simp [tone, trust,colorful,onLane,g, f,echo]
     rw [projection_eq]; change _=Real.exp (tilted P F A H y t)*_; rw [h']; change H _ * Real.exp (-(A (tone (echo P) Y₀ (t • onLane y))+r*(t • onLane y).1^2)/t^2)= Real.exp (Real.log (H (g t))-A (g t)/t^2)*_
     rw [show (t • onLane y).1=t by simp [onLane],hF, show -(A (g t)+r*t^2)/t^2=-(A (g t)/t^2) + -r from (by field_simp; ring),Real.exp_add,sub_eq_add_neg,Real.exp_add,Real.exp_log ht,mul_assoc]
   rw [show L=(fun _ => Real.exp (-r))*(Real.exp ∘ tilted P F A H y) from funext fun i=> mul_comm .., some_mul contDiffAt_const (Real.contDiff_exp.contDiffAt.comp _ hX), approves h hp he y,show someJ _=just (Real.exp (-r)) from funext fun i=> (Act.static (n:=i) _).writes _ le_rfl, exact_scale, smul_smul]
end YM.AllOrder.Response
