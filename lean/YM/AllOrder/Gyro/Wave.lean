import YM.AnalyticBridge.VERIFIED_RESET_STEP.Evaluation
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Rain.Glazing
/-!
# A sharper comparison of two actual EarlyVacuum affine prices in **different** stencils

Work at fixed period; exact heat Hessian dependence. No matching requirement on labels. The
kinetic ambiguity is sourced by stencils whose actual *cover price* carries the period charge
through the support, bought by using this TORUS linear functional exact on short stencils.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Gyro
open Function Filter Lattice RG Wilson Push Push.AbsoluteSums Precision AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration PhysicalNext MeasureTheory Finset
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}{n m:Side}{p:BudgetPoint}(d:RegularAddress n){f:Config G n→ℝ}(g:G.Simple)(H:p.Regular d.support f) (x y:Site n) (b:PlaqAxes)
section span
lemma aligns {x y o: Site n}(hx:10* separation x o<n.val)(hy:10*separation y o<n.val) (j:Axis): coord y x j = coord o x j-coord o y j:= by
 have hh : lift (x-y)= lift (x-o)-lift (y-o):= by
    apply lift_eq_iff.mpr; refine ⟨by rw [map_sub,wrap_lift,wrap_lift]; abel, fun i=> ?_⟩; have ht : (lift (x-o) i).natAbs ≤ separation x o:= component_le (x-o) i; have hv: (lift (y-o) i).natAbs ≤ separation y o:=component_le (y-o) i; rw [Pi.sub_apply]; omega
 unfold coord; rw [hh,Pi.sub_apply,Int.cast_sub]
open Averaging
-- one basis axis. avoid normalizing threshold directions here; pay elsewhere. 
def esc (G:Gauge)(b:PlaqAxes) (x:Site n):Directions G n := fun e=> if e.1=x∧b.val.2=e.2 then spike G else 0
def letter (b:PlaqAxes) (u: Site n→ℝ): Directions G n:= ∑ i,u i • esc G b i
lemma pins (u:Site n→ℝ) (e:Edge (Site n)) : letter (G:=G) b u e = if b.val.2=e.2 then u e.1 • spike G else 0 := by
 rw [letter,Finset.sum_apply,sum_eq_single e.1]; simp only [Pi.smul_apply,esc,true_and]; split_ifs <;> simp
 intro j _ h; rw [Pi.smul_apply,esc,if_neg]; exact smul_zero ..; exact fun h'=> h h'.1.symm
 simp
lemma repertoire (o:Site n): letter (G:=G) b (fun i:Site n=> coord o i b.val.1) = (wedge b (spike G)).field o:= by ext1 i; rw [pins,wedge_field]
include g H
lemma song (h: Nonwrapping d.support d.site) (hn:4≤n.val)(u: Directions G n) : logHessian f (letter b (fun _=>1)) u = 0 := by
 let vt : LinearJet G:= ⟨fun i=> if b.val.2=i then spike G else 0,0⟩
 have he : vt.positive=0:=by funext i; simp [LinearJet.positive,LinearJet.curl,vt]
 have hv: letter b (fun _:Site n=>1)=vt.field d.site:=funext fun e=>by rw [pins]; simp only [LinearJet.field,Pi.zero_apply,smul_zero,sum_const_zero,add_zero,vt, one_smul] -- maybe sigma incompat
 obtain ⟨s,hs⟩:=LinearJet.gradient_agrees vt h hn he; rw [hv]; exact ((hessian_agrees g H hs (show Agrees d.support u u from fun _ _ _=>rfl)).symm.trans (hessian_gradient g H _ _))
lemma key_off (h:x ∉ d.support)(y:Directions G n):logHessian f (esc G b x) y=0:= by
 have ht:Agrees d.support (esc G b x) 0 := by intros e he _; change (if e.1=x ∧ b.val.2=e.2 then spike G else 0)=0; exact if_neg (fun (hc:e.1=x ∧ b.val.2=e.2)=> h (hc.1 ▸ he))
 rw [hessian_agrees g H ht (show Agrees d.support y y from fun _ _ _=>rfl),hessian_eq,map_zero]; rfl
omit g H in
lemma letters_bill (f:Config G n→ℝ)(ξ η : Site n→ℝ) : logHessian f (letter b ξ) (letter b η)=∑ x, ∑ y, ξ x*η y* logHessian f (esc G b x) (esc G b y):= by
 simp only [letter,hessian_eq,map_sum,map_smul,_root_.sum_apply,smul_apply,smul_eq_mul]; simp_rw [mul_sum,mul_assoc]; rw [Finset.sum_comm]; simp only [mul_left_comm (η _) (ξ _)]
-- minimize polynomial eval exact scalar instead of sum pair nearly cancelling. true mesh Hess slope transfer
def meter (f:Pot G n) (b:PlaqAxes): ℝ := -(∑ x: Site n, ∑ y: Site n, coord x y b.val.1 ^ 2 * logHessian f (esc G b x) (esc G b y))/2
lemma reads (hn:4≤n.val)(h:Nonwrapping d.support d.site):meter f b= coeff f d.site b b:= by
 let e:= fun x:Site n=> coord d.site x b.val.1; let f₂:=fun x y:Site n=> logHessian f (esc G b x) (esc G b y)
 have hx : logHessian f (letter b e) (letter b e) = coeff f d.site b b:= by unfold e; rw [repertoire]; rfl
 have he₂ x y: coord x y b.val.1 ^2*f₂ x y=(e y^2*f₂ x y + e x^2*f₂ x y) - 2*(e x*e y*f₂ x y):= by
     by_cases hv:x∈d.support; swap; · simp [f₂,key_off _ g H _ _ hv]
     by_cases hm:y∈d.support; swap; · rw [show f₂ x y=0 from (hessian_symm H _ _).trans (key_off _ g H _ _ hm _)]; ring
     unfold e; rw [aligns (h _ hm) (h _ hv)]; ring
 have hp:∑ x:Site n, ∑ y:Site n, e y^2*f₂ x y=0:= by convert song _ g H b h hn (letter b (fun i:Site n=> e i^2)) using 1; simp [letters_bill,f₂]
 have hq:∑ x:Site n,∑ y:Site n,e x^2*f₂ x y=0:= by rw [Finset.sum_comm]; convert hp using 1; refine Finset.sum_congr rfl fun i hi=> Finset.sum_congr rfl fun j hj=>?_ ; rw [show f₂ j i= f₂ i j from hessian_symm H ..] -- equality names inspect
 rw [letters_bill] at hx; change -(∑ x,∑ y,coord x y b.val.1 ^2*f₂ x y)/2= _; rw [← hx];  simp only [he₂,sum_sub_distrib,sum_add_distrib,hp,hq]; simp_rw [←mul_sum]; unfold f₂; ring
end span
end YM.AllOrder.Gyro
