import YM.AnalyticBridge.VERIFIED_RESET_STEP.Projection
import YM.Juniper.Bright.Yarn
import YM.Pert.Kinetic.Port
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.Cinch
open Function Filter Metric Lattice Wilson RG PhysicalNext PhysicalNext.Repeat
open Push Push.AbsoluteSums AnalyticBridge VerifiedReset Collection Averaging
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G: Gauge}{c:Side}{X:Support c}{W:BudgetPoint}
local notation "p"=> Averaging.axes01
/-!
# Exponential THERMAL rigidity at PRE-DEPLOY aperture
 Shift-hessian with exact PERIOD tensor sign-log elements. Cost exponent uses TRUE minimal winding query, improving old perturbative Port bound for beta ambiguity (so BASE Price checkout can re-place coupling EXACTLY, not an assumed estimate about "small enough n").
 -/
section geometry
variable (hG:G.Simple){f:Config G c → ℝ}
local notation "ι"=> spike G
local notation "a"=> axes01.val.1
local notation "b"=> axes01.val.2
local notation "V"=> Directions G c
local notation "H"=> logHessian
-- coordinate at lifted site.
def spot (G:Gauge) {c:Side} (x:Site c): Directions G c := Pi.single (x,b) (spike G)
def lay (G:Gauge){c:Side}(x:Site c):= (wedge p (spike G)).field x
lemma formula (x:Site c): lay G x=∑ i:Site c, VerifiedReset.coord x i a • spot G i:= by
    funext j; rcases j with ⟨z,w⟩
    rw [Finset.sum_apply]; by_cases hg:b=w; subst w
    · simp [Pi.smul_apply,spot,lay,wedge_field,Pi.single_apply,smul_ite]
    simp [Pi.smul_apply, spot, lay, wedge_field,hg]
lemma flatten (G:Gauge){c : Side}: (∑ i:Site c, spot G i)=fun j:Edge (Site c)=> if b=j.2 then spike G else 0:=by
    funext j; rcases j with ⟨z,w⟩ ; rw [Finset.sum_apply]; by_cases hg:b=w; subst w; · simp [Pi.single_apply, spot]
    simp [spot,hg]
lemma meter (x y o:Site c)(hx:10*separation x o<c.val)(hy:10*separation y o<c.val) : VerifiedReset.coord x y a = VerifiedReset.coord o y a - VerifiedReset.coord o x a:=by
    have h:lift (y-x)=lift (y-o)-lift (x-o):= by
       refine lift_eq_iff.mpr ⟨?_,fun i=>?_⟩; · rw [map_sub,wrap_lift,wrap_lift]; abel
       dsimp; have hg : (lift (y-o) i).natAbs≤ separation y o:=component_le ..; have hb: (lift (x-o) i).natAbs≤ separation x o:=component_le ..; omega
    unfold VerifiedReset.coord; rw [h]; simp
-- use ANY center.
variable {o:Site c} (h: W.Regular X f)
def pullback (x : Site c) (z:Site c):= (H f (spot G x) (spot G z))
local notation "Ω"=> (pullback (f:=f))
include hG h
lemma clears (hz:Nonwrapping X o) (he:4 ≤ c.val)(x:Site c) : ∑ i:Site c,Ω x i=0:=by
    let V':= (∑ i:Site c, spot G i); let u:LinearJet G:=⟨fun j=> if b=j then ι else 0,0⟩; have ht:u.field o=V':= by ext1; unfold V'; rw [flatten]; simp [LinearJet.field,u]
    have hh:H f (u.field o) (spot G x)=0:= by
       obtain ⟨s,hs⟩:= u.gradient_agrees hz he (by ext1; simp [u,LinearJet.positive,LinearJet.curl]); exact (hessian_agrees hG h (show _ from hs) (show Agrees X (spot G x) (spot G x) from fun _ _ _ =>rfl)).symm.trans (hessian_gradient hG h s _)
    unfold pullback; rw [ht,hessian_symm h] at hh; simp_rw [hessian_eq]; unfold V' at hh; simpa only [hessian_eq,map_sum] using hh
omit hG in
lemma twist (x y:Site c): Ω x y=Ω y x:=hessian_symm h .. -- omit
lemma inactive (x y:Site c)(ht:y∉X):Ω x y = 0:=by
    have he: Agrees X (spot G y) (0:Directions G c):= fun i hi hs=> Pi.single_eq_of_ne (show i ≠ (y,b) from (fun hz=> ht ((show i.1=y from congr_arg Prod.fst hz) ▸ (show i.1∈X from hi)))) _
    unfold pullback; rw [hessian_agrees hG h (show Agrees X (spot G x) (spot G x) from fun _ _ _=>rfl) he,hessian_eq,map_zero]
-- exact summed bilinear telescope.
def coke (f:Config G c →ℝ) := ∑ i:Site c,∑ j:Site c,(VerifiedReset.coord i j a)^2 * (pullback (f:=f) i j)
lemma aimed (hn: 4 ≤ c.val) (hz: Nonwrapping X o) : coke f= -(2*H f (lay G o) (lay G o)):= by
    let d j := VerifiedReset.coord o j a
    let s := ∑ i:Site c, ∑ j:Site c, (d j-d i)^2 * Ω i j
    have hr : coke f=s:= by
       apply Finset.sum_congr rfl; intro i _; refine Finset.sum_congr rfl fun j _=>?_ ; by_cases he:i∈X <;> by_cases hJ:j∈X
       · rw [meter i j o (hz i he) (hz j hJ)]
       · rw [inactive hG h i j hJ]; simp
       · rw [twist h, inactive hG h j i he]; simp
       rw [inactive hG h i j hJ]; simp
    have ht (x:Site c):∑ i:Site c,Ω i x=0:=by rw [show (∑ i:Site c,Ω i x)=_ from Finset.sum_congr (s₁:=Finset.univ) rfl fun i _=>(twist h i x)]; exact clears hG h hz hn x
    let u:= ∑ i:Site c, ∑ j:Site c,d i * (d j * Ω i j)
    have hv: u=H f (lay G o) (lay G o):= by
       simp only [pullback, u,d,hessian_eq,formula o,map_sum, map_smul, smul_apply, smul_eq_mul, Finset.mul_sum,_root_.sum_apply]; -- orientation edit
       refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=>?_ ; rw [show fderiv ℝ (fderiv ℝ (germ f)) 0 (spot G i) (spot G j)= _ from (hessian_eq ..).symm.trans ((twist h i j).trans (hessian_eq ..))]
    rw [hr,←hv]; unfold u s
    let k:= ∑ i:Site c, ∑ j:Site c, d j^2*Ω i j
    have hₖ:k=0:= by unfold k; rw [Finset.sum_comm]; simp_rw [← Finset.mul_sum, ht, mul_zero]; simp
    have hP: (∑ i:Site c, ∑ j:Site c, (d i)^2*Ω i j)=0:= by simp_rw [← Finset.mul_sum, clears hG h hz hn, mul_zero]; simp
    simp_rw [show ∀ i j:Site c,(d j-d i)^2 * Ω i j= d j^2*Ω i j + d i^2*Ω i j - 2*(d i*(d j* Ω i j)) from fun i j=>by ring,Finset.sum_sub_distrib, ← Finset.mul_sum,Finset.sum_add_distrib]; unfold k at hₖ; rw [hₖ,hP]; ring
lemma tip (d: RegularAddress c) (hn:4≤ c.val)(hz:d.support=X)(hh:Nonwrapping (expand d) d.site): coke f= -(2*projection d f p p):= by
   rw [projection, if_pos hh]; exact aimed hG h hn (fun i hi=> hh i (Finset.mem_union_left _ (hz.symm ▸ hi)))
end geometry
end YM.Juniper.Cinch
