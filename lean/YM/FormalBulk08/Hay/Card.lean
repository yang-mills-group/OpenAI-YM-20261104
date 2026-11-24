import YM.FormalBulk08.Hay.Fits

/-! Near this graph, the unmasked germs. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Hay
open Filter Set Function MeasureTheory Lattice RG Exterior Wilson Precision Tree Work.F05
open Stationary hiding shine Rays
open Reef Series Wick Jets Orb Plait
open scoped BigOperators Topology Classical ContDiff Matrix.Norms.Frobenius Matrix
variable {G:Gauge}{c f:Side}{S:StepData c f}(F:Forest S.ratio)
variable (u: S.Choices)(p:Clip)(R:PathData G)(A: ChartRatio G)
variable (Y:Bid.Dir G c→AxisChart G F)(H: Critical F p R Y)

def hill (x:Link G c):= (stand G F).symm (Y (arm G c 1 x))
def summit (y:Rot F G):= rectum F (Lshift (hill F Y) y)
def packX (y:Rot F G):= stand G F (boxcar (hill F Y) y)
def bankS (y:Rot F G):= arm G c 1 (secondL y)
def pending (x:Rot F G):= tested F u p R (bankS F x) (packX F Y x)
def loopS (x:Rot F G):= turnSeries (m:=f) R.loop (offer G F (summit F Y x))
def heatS (x:Rot F G):= sap F A (boxcar (hill F Y) x)
def wambu : Rot F G→ℝ:= (Real.log ∘ heatS F A Y)- loopS F R Y
lemma packed x: packX F Y x=stand G F (firstL x)+Y (bankS F x):= by unfold packX boxcar bankS;rw [map_add,hill,(stand G F).apply_symm_apply]
include H
lemma hill_origin : hill F Y 0=0:= by rw [hill,map_zero, H.1,map_zero]
lemma hill_path : ContDiffAt ℝ ω (hill F Y) 0:= ContDiffAt.comp (g:= (stand G F).symm) _ (stand G F).symm.contDiff.contDiffAt <| ContDiffAt.comp 0 (g:=Y) (f:=arm G c 1) (by rw [map_zero];exact H.2.1) (arm G c 1).contDiff.contDiffAt
lemma summit_zero : summit F Y 0=0:= by rw [summit,coal_zero (hill_origin F p R Y H),rect_zero]
lemma summit_pay : ContDiffAt ℝ ω (summit F Y) 0:= ContDiffAt.comp (g:=rectum F) _ (by rw [coal_zero (hill_origin F p R Y H)];exact rect_so F) (tilt_health (hill_path F p R Y H))
lemma pack_zero : packX F Y 0=0:= by rw [packed,show firstL _=0 from rfl,map_zero,bankS,show secondL _=0 from rfl,map_zero,H.1,zero_add]
omit H in
lemma bank_zero : bankS (F:=F) (G:=G) 0=0:= map_zero (arm _ _ _)
omit H in
lemma bank_caps : ContDiffAt ℝ ω (bankS (F:=F) (G:=G)) 0:= ContDiffAt.comp _ (arm G c 1).contDiff.contDiffAt (second_lit ..)
lemma box_caps : ContDiffAt ℝ ω (boxcar (hill F Y)) 0:= by
   have hv:= tilt_health (hill_path F p R Y H)
   apply ContDiffAt.congr_of_eventuallyEq -- no
   exact ContDiffAt.comp (f:=Lshift (hill F Y)) _ (first_lit _ _) hv
   exact Eventually.of_forall fun x=> rfl
lemma pack_lit : ContDiffAt ℝ ω (packX F Y) 0:=ContDiffAt.comp _ (stand G F).contDiff.contDiffAt (box_caps F p R Y H)
lemma pend_lit : ContDiffAt ℝ ω (pending F u p R Y) 0:= by
    let f y:=(bankS F y, packX F Y y); have he: f 0=0:= by unfold f;rw [bank_zero,pack_zero F p R Y H];rfl
    exact (show ContDiffAt ℝ ω _ (f 0) from he.symm ▸ (H.2.2 u).1).comp _ ((bank_caps F).prodMk (pack_lit F p R Y H))
lemma ferry_light : ∀ᶠ x:Rot F G in 𝓝 0,input G f (offer G F (summit F Y x))= lifting F (represent (bankS F x)) (packX F Y x) := by
    let V:=Lshift (hill F Y); have he:Tendsto V (𝓝 0) (𝓝 0):= by simpa only [V,coal_zero (hill_origin F p R Y H)] using (tilt_health (hill_path F p R Y H)).continuousAt.tendsto
    filter_upwards [he.eventually (cope_pay F)] with x hx;rw [sips,summit,hx];rfl
lemma wing_bank : ∀ᶠ x: Rot F G in 𝓝 0,dollars (summit F Y) x=dollars (rectum F) (Lshift (hill F Y) x) := by
    let V:=Lshift (hill F Y); let L:=rectum F (G:=G); have he: ContDiffAt ℝ ω V 0:=tilt_health (hill_path F p R Y H); have hv:Tendsto V (𝓝 0) (𝓝 0):= by simpa only [V,coal_zero (hill_origin F p R Y H)] using he.continuousAt.tendsto
    filter_upwards [he.eventually (by simp),hv.eventually ((rect_so (G:=G) F).eventually (by simp))] with x hx hP; exact money_roller _ _ x (hP.differentiableAt (by simp)) (hx.differentiableAt (by simp))
lemma summit_score : dollars (summit F Y) 0=1:= by rw [(wing_bank F p R Y H).self_of_nhds,coal_zero (hill_origin F p R Y H),rect_score]
variable (hr:LocalRatio A)
include hr
lemma heat_cost : ContDiffAt ℝ ∞ (heatS F A Y) 0:= by
   unfold heatS; apply ContDiffAt.comp (g:=sap F A) (f:=boxcar (hill F Y)) _ _ ((box_caps F p R Y H).of_le le_top); rw [show boxcar _ 0=0 from (stand G F).injective ((pack_zero F p R Y H).trans (map_zero _).symm)]; exact sap_smooth F A hr
lemma heat_zero : heatS F A Y 0=1:= by unfold heatS; rw [show boxcar _ 0=0 from (stand G F).injective ((pack_zero F p R Y H).trans (map_zero _).symm), sap_root F A hr]
lemma tender : ∀ᶠ x:Rot F G in 𝓝 0, heatS F A Y x= sap F A (summit F Y x)*(dollars (summit F Y) x).det:= by
    let V:=Lshift (hill F Y); have hv:Tendsto V (𝓝 0) (𝓝 0):= by simpa only [V,coal_zero (hill_origin F p R Y H)] using (tilt_health (hill_path F p R Y H)).continuousAt.tendsto
    filter_upwards [wing_bank F p R Y H,hv.eventually (rect_wall F A hr)] with x hx hk;rw [hx];exact hk
variable {σ B C:ℝ}(H' : R.Bounds p σ B C)
include H'
omit hr in
lemma loop_so : ContDiffAt ℝ ω (loopS F R Y) 0:= by
   exact ContDiffAt.comp (g:=turnSeries (m:=f) R.loop) (f:=(offer G F ∘ summit F Y)) 0 (by rw [Function.comp_apply,summit_zero F p R Y H,map_zero]; exact (turns_analytic R.loop H'.width H'.two).contDiffAt) ((offer G F).contDiff.contDiffAt.comp _ (summit_pay F p R Y H))
omit hr in
lemma loop_zero : loopS F R Y 0=0:= by unfold loopS;rw [summit_zero F p R Y H,map_zero];let f:=turnSeries R.loop (m:=f); exact (rays_at_zero (f:=f) (turns_analytic R.loop H'.width H'.two)).mp ((turns_low R.loop H'.width H'.two).weaker (by omega))
lemma wambu_price : wambu F R A Y 0 =0 ∧ ContDiffAt ℝ ∞ (wambu F R A Y) 0:= by
    rw [wambu]; refine ⟨?_, ((heat_cost F p R A Y H hr).log (by rw [heat_zero F p R A Y H hr]; exact one_ne_zero)).sub ((loop_so F p R Y H H').of_le le_top)⟩; rw [Pi.sub_apply, Function.comp_apply, loop_zero F p R Y H H',heat_zero F p R A Y H hr, Real.log_one,sub_zero]
end YM.FormalBulk08.Hay
