import YM.MS.Alps.Contour
/-!
# Elementary curves from heat units (+ complex scaling weight)

All forces prescribed at p(t) implicitly. Use amplitude `a` and Euler blip.
 Rank differentiability intact, all charts, fixed z prices. Need ∂ for Pole extraction.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Alps.Bench
open Function Set Filter Finset MeasureTheory Real Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum
open Momentum Metric
open scoped Topology ContDiff
variable {E F I: Type}[NormedAddCommGroup E][NormedSpace ℝ E]
 [NormedAddCommGroup F][NormedSpace ℝ F]
namespace Forest
-- true E→ℂ
def patch (f:E→ℂ)(a:ℂ)(t:ℝ): E→ℂ := fun x=> amount a t * f (exp t • x)
def loadC (f:E→ℂ)(a:ℂ) : E→ ℂ:= fun x=> a*f x + fderiv ℝ f x x
variable {f:E→ℂ}
lemma bit (h:ContDiff ℝ ∞ f)(a:ℂ): ContDiff ℝ ∞ (loadC f a):= (contDiff_const.mul h).add (((contDiff_infty_iff_fderiv.mp h).2).clm_apply contDiff_id)
lemma patch_w (h:ContDiff ℝ ∞ f)(a:ℂ): ContDiff ℝ ∞ (Function.uncurry (patch f a)):= by unfold patch uncurry amount; change ContDiff ℝ ∞ (fun x:ℝ×E=>Complex.exp ((Complex.ofRealCLM x.1)*a) * f (exp x.1 • x.2)); fun_prop
lemma patch_d (h:ContDiff ℝ ∞ f)(a:ℂ)(x:E)(p:ℝ): HasDerivAt (fun i=> patch f a i x) ( patch (loadC f a) a p x) p:= by
    let F (p:ℝ):=exp p • x; have he:= (amountD a p).mul ((h.differentiable (by simp) _|>.hasFDerivAt.comp_hasDerivAt p ((Real.hasDerivAt_exp p).smul_const x))); convert! he using 1; unfold patch loadC; simp only [Function.comp_apply]; ring
lemma plot (h:ContDiff ℝ ∞ f)(a:ℂ): BothZ (patch f a) (patch (loadC f a) a) := {
    part s:= (patch_w h a).comp (show ContDiff ℝ ∞ (fun x:E=> (s,x)) by fun_prop)
    whole:=patch_w (bit h a) _
    deriv x p:=patch_d h a x p }
-- scaled local $Y data.$
abbrev Told (f:E→ℂ):= veg 0 (fun _:Unit=> f) 1
abbrev Vign (f:E→ℂ):= rails 0 (fun _:Unit=>1) (fun _=>f)

variable {t:ℝ}
lemma page (i:Trail0 t): t-1≤ (i:ℝ) ∧ (i:ℝ)≤ t+1 := by have hx : (i:ℝ)∈closedBall t 1:= i.property; rw [ mem_closedBall_iff_norm,Real.norm_eq_abs, abs_le] at hx; constructor <;> linarith
lemma rent (H:Told f)(a:ℂ)(t:ℝ): veg 0 (fun i:Trail0 t=>patch f a i) 1:= by convert! (Costs.mul (at_rate (E:=E) (guard_price (z:=(0:UScale (Trail0 t))) (fun i:Trail0 t=> (page i).2) (fun i:Trail0 t=> (page i).1) a)) (limitF (around H) (fun i:Trail0 t=> (page i).2))) using 1; ext; simp
lemma unrent (H: Vign f)(a:ℂ)(t:ℝ): rails 0 1 (fun i:Trail0 t=> patch f a i):= by
   let T:= (fun i:Trail0 t=>(i:ℝ)); convert! Plum.rails_mul (limitL (arced H) (fun i:Trail0 t=> (page i).1) (fun i=> (page i).2)) (at_rate (z:=0) (guard_price (v:=T) (fun i=>(page i).2) (fun i=> (page i).1) a)) using 1 -- syntax
   · ext; simp
   funext i x; exact mul_comm ..
-- plate price Euler
lemma at_id : veg 0 (fun _:Unit => fun x:E=>x) 1:= by
   convert! Scale.rescaled (Arc.path (0:UScale Unit)) (f:=(id:E→E)) Function.HasTemperateGrowth.id using 1; ext; simp -- target Scalar v
lemma board (h:Told f)(a:ℂ): Told (loadC f a):= by
   have hV : veg 0 (fun _:Unit=>fderiv ℝ f) 1:= by simpa only [cheap_length,mul_one,Told] using h.fderiv
   let Q:= ContinuousLinearMap.apply ℝ ℂ (E:=E); apply Costs.add (h.L (ContinuousLinearMap.mul ℝ ℂ a)); convert Costs.bilinear Q at_id hV using 1; rfl; simp
lemma rails_f' (h: Vign f)(a:ℂ): Vign (loadC f a):= by
   let A:=ContinuousLinearMap.fst ℝ E ℝ; let J:=ContinuousLinearMap.inl ℝ E ℝ; let V:= (ContinuousLinearMap.apply ℝ ℂ (E:=E)).flip; let S:=Arc.path (0:UScale Unit)
   have hh:Line S (fun _=>Set.univ) (fun _:Unit=>fderiv ℝ f) 1:= fun j=> by
       obtain hv := (h j).fderiv; simpa only [S,Pi.one_apply, cheap_length,mul_one] using hv
   intro b; refine Costs.add ( (h b).L (ContinuousLinearMap.mul ℝ ℂ a)) ?_; have ht: Ultra (fun p:E × ℝ=> V ( fderiv ℝ f p.1) p.1):= by
       convert! Rapid.bilinear V (Line.rapid hh) (Bound.linear A at_id) using 1; ext; simp -- order convert
   refine ?_; have he:= Costs.linear (D:= (Arc.path (0:UScale Unit)).strict fun u=> (Set.univ: Set E)) J (ht b) (fun _ _ _=> Set.mem_univ _) ⟨1,zero_lt_one,1,fun i p hp=> by simp [J,Scale.strict,Scale.slow,Scale.full]⟩; exact he
lemma Zed (h:Told f)(t:ℝ)(a:ℂ): veg (0:UScale (Trail0 t)) (fragment (patch f a) (patch (loadC f a) a t) t) (flag t):= by
   let Y:= loadC f a; have he:=board h a; let X:=plot (h.smooth ()) a; let D(x:E):= ((windowP t).full).cheap (⟨t,mem_closedBall_self zero_le_one⟩:Trail0 t) x
   convert! BothZ.brink X (plot (he.smooth ()) a) t (D:=D) (E':=fun _=>1) (fun x=>((windowP t).full).one_le _ x (mem_univ _)) (rent (board he a) a t) using 1; ext; simp -- change
lemma DimL (h:Vign f)(t:ℝ)(a:ℂ): rails (0:UScale (Trail0 t)) (flag t) (fragment (patch f a) (patch (loadC f a) a t) t) := by
    intro b; let V:=rails_f' h a; let p(x:E):=1/(1+‖x‖)^b;
    let S:=windowP t; have hN(x:E):1≤S.basic (⟨t,mem_closedBall_self zero_le_one⟩:Trail0 t):= S.one_le _; convert! BothZ.brink (plot ((railto h).smooth ()) a) (plot ((railto V).smooth ()) a) t hN (E':= p) ?_ using 1 -- tactic dance
    · ext; simp [p,Scale.weight,div_eq_mul_inv]
    convert! (unrent (rails_f' V a) a t b) using 1; ext; simp [p,Scale.weight,div_eq_mul_inv]
end Forest
end YM.MS.Alps.Bench
