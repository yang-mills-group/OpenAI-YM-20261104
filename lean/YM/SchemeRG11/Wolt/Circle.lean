import YM.SchemeRG11.Wolt.Correct
/-! Exterior test wave from an EXACT leafProbe. -/
noncomputable section
set_option autoImplicit false
namespace YM.SchemeRG11.Wolt
open Function Filter Asymptotics Topology MeasureTheory Metric
open Flock Lattice Pert Align Full Maxwell Haze Pile Catch World Atoll Tree Acorn Outlook Banner
open Labels Long MvPolynomial Air North
open scoped Classical Pointwise
variable {G:Gauge}{m:ℕ}{T:Align.Itinerary}{R r:ℝ}{p:ℕ → Cover}
local notation "D₁" => Atoll.land G
lemma commons (x y:Cover)(a b:Touch G): (D₁).bed (flex x a) (flex y b)=(D₁).bed (flex (x-y) a) b:=by rw [← flexD y (flex (x-y) a) b, flex_mul, show y+(x-y)=x by abel]
def puff (p:Touch G)(a:G.ColorIndex):Bevy ℝ:=fun i=> element ((D₁).windfall p) i a
abbrev Silent(p:Touch G):Prop:=∀x:Cover→ G.Color,sense (cant (Bark.ascent x)) p=0
lemma adjp (x:Cover)(a:G.ColorIndex)(p:Touch G) :
 let f(y:Cover):= -(Cellular.coverLine (x-y)) • Maxwell.unitColor G a
 Flock.dive (puff p a) x = sense (cant (Bark.ascent f)) p:=by
 intro f; induction p using Finsupp.induction_linear with
 | zero=> unfold puff; simp only [map_zero]; change Flock.dive (E:=ℝ) 0 x=0; rw [map_zero];rfl -- check
 | add p q hp hq=>rw [show puff (p+q) a=puff p a+puff q a from by unfold puff; simp only [map_add];rfl,map_add,map_add]; exact congrArg₂ (·+·) hp hq
 | single i b=>
    rw [show Finsupp.single i b=b • idi i by simp [idi],map_smul,show puff (b • idi i) a=b • puff (idi i) a from by unfold puff; rw [_root_.map_smul];rfl,map_smul,Pi.smul_apply]
    apply congrArg (b • ·); unfold puff; rw [grain,North.sense_single i]; let c:= unitColor G i.2 a
    have ht: (fun j=>element (cant (linkup (plumage (beat i) (unitColor G i.2)))) j a)= c • beat i:=by funext j k; exact mul_comm .. -- annotate
    rw [ht,map_smul,dive_wave,Pi.smul_apply,rear_apply]
    let p:=i.1.1; let j:=i.1.2
    change unitColor G i.2 a *(Φ (x-p)-Φ (x-step j-p))= ((-Φ (x-(p+step j))) • unitColor G a - (-Φ (x-p)) • unitColor G a) i.2
    rw [sub_right_comm,sub_sub]; simp only [PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul,unitPaint]; by_cases H:a=i.2<;>simp [H,Ne.symm]; ring -- plus addition order
lemma quiet (p:Touch G)(h:Silent p)(z:Cover): Silent (flex z p):=by
 intro x; rw [flex_eval]; rw [show tuck (cant (Bark.ascent x)) z=cant (Bark.ascent (hop z x)) from ?_]; exact h _
 funext q; change (x (q.1.1+z+step q.1.2)-x _) _=(x (q.1.1+step q.1.2+z)- x _) _; rw [add_right_comm];rfl
lemma paceE {y:E4}(h:Along T p y)(hc:2*R<‖y‖)(x:Cover):∀ᶠ i in atTop, ¬Near T R i (x+p i):=by
 have he:= h.shift x; filter_upwards [(Tendsto.norm he).eventually (lt_mem_nhds hc)] with i hi hv
 rw [add_comm x] at hv; exact not_lt.mpr ((cord T i _).trans (mul_le_mul_of_nonneg_left hv (by positivity))) hi
lemma voided {y:E4}(h:Along T p y)(hc: 2*R < ‖y‖)(a:Touch G)(u:G.ColorIndex):∀ᶠ i in atTop,∀j:Axis,∀x,Near T R i x→ lap (puff (flex (p i) a) u j) x=0:=by
 induction a using Finsupp.induction_linear with
 | zero=> filter_upwards with i j x hx; unfold puff; simp only [map_zero]; exact congrFun (map_zero lap) _
 | add a b ha hb=> filter_upwards [ha,hb] with i ha hb j x hx; rw [map_add, show puff _ u j=puff (flex (p i) a) u j+puff (flex (p i) b) u j from by unfold puff; simp only [map_add];rfl,map_add]; simp only [Pi.add_apply,ha j x hx,hb j x hx, add_zero]
 | single a b=>
    filter_upwards [paceE h hc a.1.1] with i hi j x hx
    let r:=Acorn.rise (p i) a
    rw [show Finsupp.single a b=b • idi a by simp [idi], (flex _).map_smul,flex_one]; unfold puff; rw [_root_.map_smul (D₁).windfall, North.sense_single]; let V:= unitColor G r.2 u
    have hw: element (b • cant (linkup (plumage (beat r) (unitColor G r.2)))) j u = b • (V • beat r j):=by funext k; change b*(beat _ _ _ * unitColor _ _ _)=b*(V*_); rw [mul_comm (beat _ _ _)]
    rw [hw,map_smul, Pi.smul_apply,map_smul,Pi.smul_apply]; suffices H:lap (beat r j) x=0 by rw [H,smul_zero,smul_zero]
    unfold beat; split
    · rw [lap_p,if_neg (show x≠ r.1.1 from fun w=>hi (show Near T R i r.1.1 from w ▸ hx)),neg_zero]
    exact congrFun (map_zero lap) x
lemma strikes {y:E4}(h:Along T p y)(hc: 2*R < ‖y‖) (v:Touch G)(hp:Silent v)(a:ℕ→ℝ)(c:G.ColorIndex): keeps T R (ribbon (fun i=>(D₁).windfall (a i • flex (p i) v)) c):=by
 filter_upwards [voided h hc v c] with i hi x hx
 have he (w:Touch G): ribbon (fun _ : ℕ=>(D₁).windfall (a i • w)) c i= a i • puff w c:=by unfold ribbon puff; rw [_root_.map_smul];rfl -- D₁ notation
 change Flock.dive (ribbon _ c i) x=0 ∧ _; rw [show ribbon (fun k=>(D₁).windfall (a k • flex (p k) v)) c i= _ from he (flex (p i) v)]
 rw [map_smul, Pi.smul_apply]; refine ⟨?_,fun j=>?_⟩
 · rw [adjp, quiet v hp,smul_zero]
 rw [Pi.smul_apply,map_smul,Pi.smul_apply,hi j x hx, smul_zero]
end YM.SchemeRG11.Wolt
