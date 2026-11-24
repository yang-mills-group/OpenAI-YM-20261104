import YM.MS.Alps.Mattel
/-!
# Exponential chords, rates to nearest horizon

Use ∀ data and times, denominators don't involve `g` or pole. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Alps
open Function Set Filter Finset MeasureTheory Real Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum
open Momentum Metric
open scoped Topology ContDiff Interval
variable {E F I: Type} {G:Gauge}{b c:Bool}{p t:ℝ}
variable {u v:ℝ→ Mob G}{r:ℝ→ Rip G}{H Y: Mob G}{V: Rip G}

def sp (t:ℝ)(x:Trail0 t): ℝ:= |cord t x|
lemma nn0 (t:ℝ)(x:Trail0 t): 0≤ sp t x:= abs_nonneg _
lemma short (t:ℝ)(x:Trail0 t): sp t x ≤ 1:= by obtain hx:= x.property; change x.val∈closedBall t 1 at hx; exact mem_closedBall_iff_norm.mp hx
lemma flag_nn (t:ℝ)(x:Trail0 t): 0≤ flag t x:= sq_nonneg _
lemma between (t:ℝ)(x:Trail0 t): flag t x=(sp t x)^2:= by simp [flag,sp]
lemma low (t:ℝ)(x:Trail0 t): flag t x≤ sp t x:= by rw [between,pow_two]; exact mul_le_of_le_one_left (nn0 ..) (short ..)
lemma climb_sc {z:UScale I}{u:I→Rip G}{c:I→ℂ}{a b:I→ℝ}(h:rib z a u)(hx:scaleC z b fun i=>‖c i‖): rib z (fun i=> a i*b i) (fun i=>c i • u i):= by intro m i j; convert! rails_mul (h m i j) (at_rate hx) using 1; funext n x; exact mul_comm ..
lemma knot_v (h: BeamR r V t)(hv:rPrice V): rib 0 (sp t) fun i=> r i.val - r t:= by
   let s:= sp t; have he : scaleC 0 s fun i=> ‖(cord t i:ℂ)‖ := Cost.of_le fun i p _=> by simp [s,sp,Real.norm_eq_abs]
   have hm:=climb_sc (u:=fun _:Trail0 t=>V) (transport hv) he; convert! r_add ( climb h.pay (low t)) (show rib 0 (sp t) (fun i=>(cord t i:ℂ) • V) from ?_) using 1; · funext i; exact (sub_add_cancel _ _).symm;
   simpa only [Pi.one_apply,s,one_mul] using hm
lemma curve_v (h: Curve u H t)(hv:kPrice H): fell 0 (sp t) fun i=> u i.val-u t:= by
   have he : scaleC 0 (sp t) fun i=> ‖(cord t i:ℂ)‖ := Cost.of_le fun i p _=> by simp [sp,Real.norm_eq_abs]
   have hm:= fall_scale (f:=fun _:Trail0 t=>H) (travel hv) he; convert! fall_add ( trust h.pay (low t)) (show fell 0 (sp t) (fun i=>(cord t i:ℂ) • H) from ?_) using 1; · funext i; exact (sub_add_cancel _ _).symm;
   simpa only [Pi.one_apply,mul_one] using hm
lemma Curve.add (h:Curve u H t)(hv:Curve v Y t): Curve (u+v) (H+Y) t:=by refine ⟨?_⟩; convert! fall_add h.pay hv.pay using 1; funext i; simp only [polar,Pi.add_apply,smul_add]; abel
lemma Curve.scale (c:ℂ)(h:Curve u H t): Curve (c • u) (c • H) t:= by refine ⟨?_⟩; rw [show polar _ _ t= c • polar u H t from funext fun i=> by simp only [polar,Pi.smul_apply,smul_comm c (cord t i:ℂ),smul_sub] ]; convert fall_scale (U:=fun _=>c) h.pay (const_sc (z:=(0:UScale (Trail0 t))) .. ) using 1; simp; rfl -- simplify c/cord
lemma Curve.zero : Curve (0:ℝ→Mob G) 0 t := by refine ⟨?_⟩; convert! fall_zero (G:=G) (z:=0) (flag_nn t) using 1; ext; simp [polar]
lemma Curve.sum (s:Finset I) {u:I→ℝ→ Mob G}{Y:I→Mob G}(hf:∀ i∈s,Curve (u i) (Y i) t) : Curve (∑ i∈s,u i) (∑ i∈s,Y i) t:= by
    classical
    induction s using Finset.induction_on with| empty=> simp only [Finset.sum_empty]; exact Curve.zero| insert i l hi ih=> simp_rw [Finset.sum_insert hi]; exact (hf i (by simp)).add (ih (fun a ha=>hf a (Finset.mem_insert_of_mem ha)))
end YM.MS.Alps
