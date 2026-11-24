import YM.MS.Alps.Sierra
/-!
# Hessian controlled coverage

Strong if TD(D expression) on local window near any t, supplied by Mellin sources. Derivative estimates ∂ all.
 Doesn't require a stencil chart-specific moment at $D$ poles. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Alps
open Function Set Filter Finset MeasureTheory Real Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum
open Momentum Metric
open scoped Topology ContDiff
variable {G:Gauge}{I A E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
 [NormedAddCommGroup A][NormedSpace ℝ A][CompleteSpace A]
variable {t:ℝ}{X Y Z:ℝ→ E→A}
structure BothZ (X Y:ℝ→ E→ A): Prop where
    part: ∀ i:ℝ, ContDiff ℝ ∞ (X i)
    whole: ContDiff ℝ ∞ (Function.uncurry Y)
    deriv (x:E)(t:ℝ): HasDerivAt (fun t:ℝ=>X t x) (Y t x) t
omit [CompleteSpace A] in
lemma BothZ.later (h:BothZ X Y)(t:ℝ): ContDiff ℝ ∞ (Y t) := h.whole.comp (show ContDiff ℝ ∞ (fun p:E=> (t,p)) by fun_prop)
lemma BothZ.axes (h:BothZ X Y)(t:ℝ)(j:ℕ)(x:E): HasDerivAt (fun p:ℝ=> iteratedFDeriv ℝ j (X p) x) (iteratedFDeriv ℝ j (Y t) x) t:= by
   let V (p:ℝ) (x:E):= Heat.desk (Function.uncurry Y) (p,x); have he p : ContDiff ℝ ∞ (V p) := (Heat.park h.whole).comp (show ContDiff ℝ ∞ (fun x:E=> (p,x)) by fun_prop); have hp : X=fun p=> (let a:=V p;a)+X 0:= by
       funext p x; have ht : IntervalIntegrable (fun t:ℝ=> Y t x) volume 0 p:= (h.whole.continuous.comp (show Continuous fun r:ℝ=> (r,x) by fun_prop)).intervalIntegrable 0 p; exact eq_add_of_sub_eq (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y hy=> h.deriv x y) ht).symm
   have hx p: iteratedFDeriv ℝ j (X p) x=iteratedFDeriv ℝ j (V p) x+iteratedFDeriv ℝ j (X 0) x:= by conv_lhs=> rw [hp]; rw [iteratedFDeriv_add ((he p).of_le (by exact_mod_cast le_top)) ((h.part 0).of_le (by exact_mod_cast le_top)),Pi.add_apply] -- conv
   convert! ((Heat.deskD_iter h.whole j t x).add_const (iteratedFDeriv ℝ j (X 0) x)) using 1; funext t; exact hx t
-- cost hess

def fragment (X:ℝ→ E→ A)(Z:E→ A)(t:ℝ)(i:Trail0 t) : E→ A:= X i-X t- cord t i • Z
omit [CompleteSpace A] in
lemma BothZ.smooth (h:BothZ X Y)(t:ℝ)(i:Trail0 t): ContDiff ℝ ∞ (fragment X (Y t) t i):= ((h.part _).sub (h.part t)).sub ((h.later t).const_smul _)
omit [CompleteSpace A] in
lemma BothZ.resume (h:BothZ X Y)(t:ℝ)(j:ℕ)(p:E)(i:Trail0 t) : iteratedFDeriv ℝ j (fragment X (Y t) t i) p= slopeP t (fun s=> iteratedFDeriv ℝ j (X s) p) (iteratedFDeriv ℝ j (Y t) p) i:= by
    have he : ∀ {f:E→A}, ContDiff ℝ ∞ f→ ContDiffAt ℝ (↑j) f p:= fun {f} H=> H.contDiffAt.of_le (by exact_mod_cast le_top)
    rw [fragment,iteratedFDeriv_sub_apply (f:=X i.val-X t) (g:=cord t i • Y t) (he ((h.part _).sub (h.part t))) (he ((h.later t).const_smul (cord t i))), iteratedFDeriv_sub_apply (he (h.part _)) (he (h.part t)), iteratedFDeriv_const_smul_apply (he (h.later t))]; rfl

def windowP (t:ℝ): Scale (Trail0 t) := Arc.path 0
def flag (t:ℝ)(i:Trail0 t): ℝ:= cord t i ^ 2
lemma BothZ.brink (h:BothZ X Y)(hh:BothZ Y Z)(t:ℝ){D E': E→ℝ} (hd:∀ i,1≤D i) (hc:Costs ⟨fun _:Trail0 t=>Set.univ,fun _=>D,fun _ p _=>hd p⟩ (windowP t) (fun i: Trail0 t=> Z i.val) (fun _ => E')) : Costs ⟨fun _: Trail0 t=>Set.univ,fun _=>D,fun _ p _=>hd p⟩ (windowP t) (fragment X (Y t) t) (fun i p=> flag t i * E' p):= by
   refine ⟨h.smooth t,fun j=>?_⟩; obtain ⟨C,hC,b,hb⟩:= hc.quoted j; refine ⟨C,hC,b,fun i p hp=>?_⟩
   dsimp only; rw [h.resume]
   apply le_trans (taylor2 t (fun t=> h.axes t j p) (fun t=> hh.axes t j p) (K:=C* D p^b * E' p) ?_ i ); · simp only [flag,windowP,cheap_length,one_pow,mul_one]; exact le_of_eq (by ring)
   intro x hx; simpa only [windowP,cheap_length,one_pow,mul_one] using hb (⟨x,hx⟩:Trail0 t) p (mem_univ _)
end YM.MS.Alps
