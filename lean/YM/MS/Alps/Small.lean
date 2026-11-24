import YM.MS.Alps.Valley
/-!
# Scale covariance of dimensional regulator in right-germ

No fixed Laurent power interpretation hiding exact dilation. Use Flow ∂t at any
 log length, ℓ scaling from line power mismatch. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Alps
open Function Set Filter Finset MeasureTheory Real Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum
open Momentum Metric
open scoped Topology ContDiff
variable {G:Gauge}{I A B E P:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
  [NormedAddCommGroup P][NormedSpace ℝ P]{m:ℕ}{F:Mob G}{U:Rip G}
lemma air_ocean (HF:kPrice F)(HU:rPrice U)(z a b:ℂ)(t:ℝ): ocean z (pulse a t U) (plow b t F)= plow (a+b-4-2*z) t (ocean z U F):= by
   funext m l; let w:=ray l; let v:=ray (sr t l); let V:= wing z (pulse a t U) (plow b t F) w; let W:= wing z U F v; let K:= a+b+(mass l:ℂ); let H:= Zed m
   have h (x:SectorP m)(y:ℝ): V ((x,y),1)=amount K t * W ((exp t • x,exp t*y),1):= by
       unfold V W K w v wing; dsimp only; rw [n_track a b z t, ray_sail,ray_sail,mass_lift,lift_sr,← map_smul]; rfl -- latter prod defeq
   have hh: Module.finrank ℝ (SectorP m)=H:= by simp [SectorP,H]
   let μ:= Px m; let f:= carpet μ V; let g:= carpet μ W;
   have hx y : f (y,(1:ℝ)) = amount (K-H) t*g (exp t*y,1):= by
       unfold f carpet; dsimp only; simp_rw [h]; rw [integral_const_mul, Measure.integral_comp_smul_of_nonneg μ (fun p=> W ((p,_),_)) (exp t) (hR:=(exp_pos t).le),hh]; unfold g carpet; push_cast [Complex.real_smul]; -- inspect
       rw [← Complex.ofReal_exp,amount_power,amount_inv,← mul_assoc,← amount_add]; rfl
     -- mark
   have hu : Ultra f:=carpet_test (powder HF b t) (priced1 HU a t) w z; have ht : Ultra g :=carpet_test HF HU v z
   change coreC (cloud z) m f 1= amount _ t * coreC (cloud z) m g 1; rw [estimate 1 (hu.smooth ()) (ht.smooth ()) hx z m,← amount_add, show -(2*z)+2*(m:ℂ)+(K-H)=a+b-4-2*z+ ↑(mass l) from ?_]; unfold K H Zed; push_cast; ring
-- Q relation sign per family bare. use rule one privileged weight.
def RawQ (Q: Shade G): Prop:= ∀ (m a b p t), amount (wfield b:ℤ) t * amount (-(wfield a:ℤ)) t * (Q m).table a b p * amount 1 t = (Q m).table a b (Real.exp t • p)
lemma visit_sr {b:Bool} (p:Koszul.Sector A)(t:ℝ)(U:Slash A P ℂ)(w:Legs (Mode A P)): Plane.visit b p (sr t w) U=Plane.visit b p w (fun l i r=> U (sr t l) (i.1,exp t • i.2) (sr t r)):= by induction w generalizing U with | nil=>rfl|cons a w ih=> rw [show sr t (a::w)=(a.1,exp t • a.2)::sr t w from rfl, visit_cons, ih, visit_cons]; rfl
omit [NormedAddCommGroup P] [NormedSpace ℝ P] in lemma visit_m {b:Bool} (p:Koszul.Sector A)(x:ℂ)(U:Slash A P ℂ)(w:Legs (Mode A P)): Plane.visit b p w (fun l i r=> x* U l i r)=x*Plane.visit b p w U:=by induction w generalizing U with| nil=>simp [visit_nil]| cons a w ih=> rw [visit_cons,visit_cons,ih]; ring
lemma pole_amp (Q: Shade G)(H:RawQ Q)(b:ℂ)(t:ℝ): portZ Q (plow b t F)= plow (b-1) t (portZ Q F) := by
   funext m l; simp only [plow, portZ, visit_Z, visit_sr]; -- RHS factor through visit. Need lemma `visit_s` or direct charge sensible with parity
   rw [← visit_m]; apply visit_agree; intro x i r hx; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _=> ?_; rw [← H m i.1 j i.2 t]; have he := visit_field wfield x r i j; change mass (x++(j,i.2)::r)=mass _- wfield i.1+wfield j at he; rw [hx] at he; unfold sr; rw [List.map_append,List.map_cons, he]; dsimp only; simp only [Int.cast_add,Int.cast_sub]; rw [show amount (b+(↑(mass l) - ↑(wfield i.1) + ↑(wfield j))) t=amount (b-1+ ↑(mass l)) t*amount (wfield j:ℤ) t*amount (-(wfield i.1:ℂ)) t * amount 1 t by rw [← amount_add,←amount_add,←amount_add]; congr 1; ring]; ring
end YM.MS.Alps
