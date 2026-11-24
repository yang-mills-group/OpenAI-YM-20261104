import YM.FVA2.Gen.World
import YM.MS.Cylinder.Ink
/-!
 # Commuting spatial, scale, amplitude derivatives; coefficient identification
 Analytical supplier for purely formal high-weight equality. Nothing on continuum limits here.
 -/
noncomputable section
set_option autoImplicit false
namespace YM.FVA2.Inked
open Function Filter Set Finset MeasureTheory Topology
open scoped ContDiff BigOperators Classical
open Lattice RG Gen MS.Koszul MS.Cylinder.Taylor
universe u v w
variable {E F X L : Type*}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F][NormedAddCommGroup X][NormedSpace ℝ X]{f:E × F→X}{p:E × F}{e:L→E}{a:E}{b:F}{n:ℕ}
theorem mixed_par (h:ContDiff ℝ ω f): ContDiff ℝ ω (par p f):= ( h.fderiv_right le_rfl ).clm_apply contDiff_const
lemma layerL (h:ContDiff ℝ ω f)(a:E)(p:E×F): par (a,(0:F)) f p=layer a (fun x=> f (x,p.2)) p.1:=by
    have ht : HasFDerivAt ( fun t:E=>( t,p.2) ) (ContinuousLinearMap.inl ℝ E F) p.1:= ( hasFDerivAt_id _ ).prodMk ( hasFDerivAt_const _ _ ); obtain he:=((h.differentiable (by simp) p).hasFDerivAt.comp p.1 ht).fderiv; change _=( fderiv ℝ _ _ ) _; exact (DFunLike.congr_fun he a).symm
lemma layerR (h:ContDiff ℝ ω f)(b:F)(p:E×F): par ((0:E),b) f p=layer b (fun x=> f (p.1,x)) p.2:=by
    have ht : HasFDerivAt ( fun t:F=>( p.1,t) ) (ContinuousLinearMap.inr ℝ E F) p.2:= ( hasFDerivAt_const _ _ ).prodMk ( hasFDerivAt_id _ ); obtain he:=((h.differentiable (by simp) p).hasFDerivAt.comp p.2 ht).fderiv; exact (DFunLike.congr_fun he b).symm
-- ink commutations. Continuum Seed stores complex, but these steps all real.
section
variable {f:E×F→ℝ}(h:ContDiff ℝ ω f)(b:F)(w:List L)(e)
local notation "R"=> par ((0:E),b)
local notation "X"=> w
include h
lemma ink_cons (i:L)(p:F): ink e (fun a:E=> f (a,p)) (i::w)=ink e (fun a:E=> par (e i,(0:F)) f (a,p)) w:=by exact congrArg (fun A:E→ℝ => ink e A w) ( Eq.symm ( funext fun a:E=> layerL h (e i) ( a,p ) ) )
lemma ink_c : ContDiff ℝ ω (fun y=> ink e (fun x:E=> f (x,y)) w):= by
    induction w generalizing f with | nil=> simp_rw [ink]; exact Complex.ofRealCLM.contDiff.comp ( h.comp ( f:=fun y=> ((0:E),y) ) ( contDiff_const.prodMk contDiff_id ) )| cons i l ih=> simp_rw [ink_cons e h l]; exact ih (mixed_par h)
lemma ink_peel (y:F): par b (fun y:F=> ink e (fun x:E=> f (x,y)) w ) y= ink e (fun x:E=> R f (x,y)) w:= by
    induction w generalizing f with
    | nil=> simp_rw [ink]; let A(t:F):= f ((0:E),t); change par b (Complex.ofRealCLM ∘ A) y= _; rw [ par_L (f:=A) _ (( h.comp (f:=fun t:F=>((0:E),t)) (contDiff_const.prodMk contDiff_id)).differentiable (by simp) _ ), layerR h ]; rfl
    | cons i l ih=> simp_rw [ink_cons e h l, ink_cons e (mixed_par (p:=((0:E),b)) h) l,ih (mixed_par h) ]; exact congrArg (fun A:E→ℝ=> ink e A l ) (funext fun x=> par_swap ( h.of_le le_top ))
lemma ink_contour (y:F): par b (fun y:F=> ink e (fun x:E=> f (x,y)) w ) y= ink e (fun x:E=> par b (fun t:F=> f (x,t)) y) w:=by rw [ ink_peel e h ]; simp_rw [layerR h]; rfl
end
section
variable {f:E×ℝ→ℝ} (h:ContDiff ℝ ω f)(e)(w:List L)(k:ℕ)
include h
lemma ink_t (t:ℝ): iteratedDeriv k (fun y=> ink e (fun x:E=> f (x,y)) w) t= ink e (fun a:E=> iteratedDeriv k (fun y=>f (a,y)) t) w:=by
    induction k generalizing t f with
    | zero=> simp
    | succ k ih=>
       let R:=par ((0:E),(1:ℝ)) (F:=ℝ); let K(t:ℝ):= ink e (fun a:E=> f (a,t)) w; change iteratedDeriv (k+1) K t=_; rw [ iteratedDeriv_succ', show deriv K=(fun y=> ink e (fun a:E=> R f (a,y)) w ) from funext (ink_peel e h (1:ℝ) w), ih (mixed_par h) ]; apply congrArg (fun A:E→ℝ=> ink e A w); funext a; rw [iteratedDeriv_succ', show deriv (fun t:ℝ=> f (a,t))=(fun t:ℝ=> R f (a,t)) from funext fun t:ℝ=>?_ ]; exact ( layerR h _ (a,t) ).symm
end
end YM.FVA2.Inked
