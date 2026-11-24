import YM.OPE.Compatible.Soup.Peak
/-!
# Directional derivatives in translated chamber coordinates

`turn R x` sends `y` to `x + R y`, keeping the translation introduced by fixed
exterior coordinates. `turnP`, `turnZ`, and `turnD` transport directional
derivatives, flux, and divergence through this affine chart. When the derivative
condition for `p` and the weighted divergence cancellation hold, `ere` gives
vanishing of the weighted `Stamp` integral.
-/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.OPE.Variance
open Function Filter Set MeasureTheory Lattice Wilson RG Precision Metric Matrix Cascade Finset
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{P:ChartRatio G}
attribute [local instance] Gauge.frobInner
open Next.SectorChange Stationary
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion
open Flock Libra.Shell
variable {I E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][NormedAddCommGroup F][NormedSpace ℝ F][FiniteDimensional ℝ F]
variable (R:E→L[ℝ] F)(x:F)
abbrev turn (y:E):F:= x+R y
omit [FiniteDimensional ℝ E][FiniteDimensional ℝ F] in
lemma turnB (p:ScriptJ F)(h:p.B): ScriptJ.B (p ∘ turn R x):=fun i=>(h i).comp (w:=turn R x) fun z=>by
       let f:E→ℝ:=fun e=>z (turn R x e); have hl: f=(fun _=>z x)+((z.comp R.toLinearMap):E→ℝ):=funext fun _=>map_add z ..; change Bond f; rw[hl]; exact Bond.add (Bond.keep (z x)) (Bond.glyph (z.comp R.toLinearMap)) 
omit [FiniteDimensional ℝ E] in
set_option linter.unusedSectionVars true in lemma turnP (v:E)(p:F→Token)(h:ScriptJ.B p):Pry v (p∘ turn R x)= Pry (R v) p ∘ turn R x:=by
       funext i; apply eta
       all_goals first | change fderiv _ _ _ _= fderiv _ _ _ _
       · change fderiv ℝ ((fun y=>(p y).s) ∘ turn R x) i v= _; exact dif (h 0) v i
       · change fderiv ℝ ((fun y=>(p y).l) ∘ turn R x) i v= _; exact dif (h 1) v i
       change fderiv ℝ ((fun y=>(p y).h) ∘ turn R x) i v= _; exact dif (h 2) v i
where dif {f:F→ℝ}(h:Bond f)(v y:E) :fderiv ℝ (f ∘ turn R x) y v= fderiv ℝ f (turn R x y) (R v):=by
        let H:=((hasFDerivAt_const (𝕜:=ℝ) x y).add (R.hasFDerivAt)); have hk:HasFDerivAt (turn R x) R y:=by have he:0+R=R:=zero_add _; rw[he] at H; exact H
        rw [((h.smooth.differentiable (by simp)|>.differentiableAt).hasFDerivAt.comp (g:=f) y hk).fderiv];rfl
variable (u:I→E)(Y:I→ScriptJ F)(H:Finset I)
omit [FiniteDimensional ℝ E] in
lemma turnZ (p:F→Token)(h:ScriptJ.B p):Flux u (fun i=> Y i ∘ turn R x) H (p ∘ turn R x)=Flux (fun i=>R (u i)) Y H p ∘ turn R x:=by unfold Flux; simp_rw[turnP _ _ _ _ h]; funext i; rw[Function.comp_apply,Finset.sum_apply,Finset.sum_apply];rfl
omit [FiniteDimensional ℝ E] in
lemma turnD (h:∀ i∈H,(Y i).B): divergence u (fun i=> Y i ∘ turn R x) H = divergence (fun i=>R (u i)) Y H ∘ turn R x:=by
       funext i; unfold divergence; rw[Function.comp_apply,Finset.sum_apply,Finset.sum_apply]; apply sum_congr rfl; intro j hj; rw[turnP _ _ _ _ (h j hj)]; rfl
-- Local weight in the flux identity and its integrated form.
variable (L:Law E)(X:I→ScriptJ E)(j p:ScriptJ E)
lemma heir (q:Token) (hy:j.B)(hp:p.B)(ht: ∀ i,spur (Pry (u i) p)=link L (u i))(hv:divergence u X H*j+Flux u X H j=0):
       let W:= (fun _:E=>q)*j*wheel p
       Flux u X H W+W*Flux u X H p=W*(indexQ L u X H-divergence u X H):=by
           intro W; unfold W; rw [plyFlux _ _ _ _ _ (height (Bfray q) hy) (heightens p hp),plyFlux _ _ _ _ _ (Bfray q) hy,pureFlux,zero_mul,add_zero,Prow p _ _ _ hp]; simp_rw[ht]; rw [show Flux u X H j= -(divergence u X H*j) from eq_neg_of_add_eq_zero_right hv]; unfold indexQ; ring
variable [MeasurableSpace E][BorelSpace E](μ:Measure E)[μ.IsAddHaarMeasure]
lemma ere (hY:∀ i∈H,(X i).B)(q:Token)(f:ScriptJ E)(hf:f.B)(hj:j.B)(hp:p.B)(ht:∀ i,spur (Pry (u i) p)=link L (u i))(hv:divergence u X H*j+Flux u X H j=0):
       let W:=(fun _:E=>q)*j*wheel p
       draw (W * Stamp u X H p f) L μ=0:=by
           intro W; have hh:=height (height (Bfray (E:=E) q) hj) (heightens p hp); let a:=Stamp u X H p f; have hx := Divμ L μ u X H hY W p hh hp (heir u H L X j p q hj hp ht hv) f hf;
           have he:draw (W*a + Flux u X H f*W) L μ=draw (Flux u X H p*f*W) L μ:=congr_arg (fun s=>draw s L μ) (by unfold a Stamp;ring); rw[duoS _ _ _ _ (height hh (stampL _ _ _ hY _ _ hp hf)) (height (fluxB _ _ _ hY f hf) hh), hx] at he; exact (add_eq_right.mp he) 
end YM.OPE.Variance
