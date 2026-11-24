import YM.FVA2.Gen.Path
/-! # Radial gauge realization globally -/
noncomputable section
set_option autoImplicit false
namespace YM.FVA2.Gen
open Function Finset Set Filter Topology
open scoped ContDiff BigOperators Classical Matrix.Norms.Frobenius
open Lattice RG Labels Precision Source
variable {G:Gauge}{A:Sky G}{f:Mist G}{u:E4→G.El}{x y v:E4}
local notation "P"=> E4
local notation "M"=> G.Mat
local notation "Γ"=> G.colorMat
local notation "U"=> G.mat
local notation "δ"=> par
local notation "Y"=> hat G
local notation "L"=> U ∘ u
-- one-form. finite sum positive axes
abbrev axis (A:Sky G) (x y:E4):= ∑ i:Axis, x i • A i y
lemma axis_scale (t:ℝ): axis A (t • x) y=t • axis A x y:=by unfold axis; simp [Finset.smul_sum,smul_smul]
def circle (A: Sky G) (p:E4×ℝ):=axis A p.1 (p.2 • p.1)
def Silent (B:Sky G): Prop:= ∀ x:E4, axis B x x=0
lemma cCircle (h:Fluid A): ContDiff ℝ ∞ (circle A):= by
   refine ContDiff.sum (fun i _=> ContDiff.smul (f:=fun x:E4×ℝ=> x.1 i) ?_ ( h i|>.comp (f:=fun p:E4×ℝ=>p.2 • p.1) (contDiff_snd.smul contDiff_fst) )); let E:E4→L[ℝ] ℝ:= LinearMap.toContinuousLinearMap ( { toFun p:= p i,map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl}:E4→ₗ[ℝ]ℝ ); exact E.contDiff.comp contDiff_fst -- fix
variable {p:E4→ℝ→G.El}
lemma Meets.pathway (he:Meets (circle A) p)(x:E4)(s t:ℝ): p (s • x) t=p x (s*t):= by
 let X := p (s • x); let f(t):= p x (s*t); have ht : SolvesLink f (fun t:ℝ=> circle A (s • x,t)):= by
   refine ⟨ by unfold f; rw [mul_zero]; exact ( he x ).1, ?_ ⟩; intro a; have hx : HasDerivAt (fun t:ℝ=>s*t) s a:= by simpa using! ( hasDerivAt_id' a ).const_mul s
   refine ( (( he x ).2 _).scomp a hx ).congr_deriv ?_; -- factor real mat. order
   change s • (U (f a)*Γ (axis A x ((s*a) • x)))= U (f a)*Γ (axis A (s • x) (a • s • x)); rw [ smul_smul,mul_comm a s,axis_scale,map_smul,mul_smul_comm ]
 exact Hol.agree isOpen_univ convex_univ (Set.mem_univ _) (A:=fun t:ℝ=> circle A (s • x,t)) (fun i _=> ( he _ ).2 i) (fun i _=> ht.2 i) (( he (s • x)|>.1 ).trans ht.1.symm) (Set.mem_univ _)
private lemma axes (x:E4): ∑ i:Axis,x i • basis i=x:= by ext i; simp
lemma contraction (h:Lived u): Γ (axis (skyturn u A) v x) * U (u x) = U (u x)*Γ (axis A v x)- par v (U∘u) x:=by
    have he: par v (U∘u) x= ∑ i:Axis,v i • par (basis i) (U∘u) x:= by
       let D:=fderiv ℝ (U∘u) x; change D v=_; conv_lhs=> rhs; rw [← axes v]; -- note lambda focus
       rw [ map_sum ]; exact sum_congr rfl fun i _=> map_smul D ..
    unfold axis; simp_rw [ he,map_sum, map_smul, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, ← sum_sub_distrib ]; apply sum_congr rfl; intro i _; rw [ show Γ (skyturn u A i x) * _= _ from skyline (i:=i) h, smul_sub ]; rfl -- he maybe no match

-- ∂H along t = continuation φ. Derive via contraction.
lemma still_τ (he:Meets (circle A) p)(hp:Fluid A): ∃ u:E4→ G.El, Lived u ∧ u 0=1 ∧ Fluid (skyturn u A) ∧ Silent (skyturn u A):= by
 let Ux(x:E4):= p x 1; have hx: Lived Ux:= he.smooth ( cCircle hp ); have hu: Ux 0=1:= by unfold Ux; rw [show (0:E4)=( (0:ℝ) • (0:E4) ) from (zero_smul ..).symm, Meets.pathway he, zero_mul]; exact (he 0).1
 refine ⟨Ux,hx,hu,skyline_sm hx hp,fun y=>?_ ⟩ -- note hx implicit infer
 let V:= skyturn Ux A; have hD : par y (U ∘ Ux) y = U (Ux y) * Γ (axis A y y):= by
    have ht(t:ℝ): Ux ( (0:E4)+t • y)=p y t:= by rw [ zero_add]; unfold Ux; rw [Meets.pathway he,mul_one ]
    obtain hz:= par_line ( hx.differentiable (by simp) ) y 0 1; simp only [one_smul,zero_add] at hz; simp_rw [ Function.comp_apply,show ∀ t:ℝ,Ux (t • y)=p y t from (fun t=> by simpa using ht t) ] at hz; exact hz.unique ( by obtain h:=( he y ).2 1; simp only [circle,one_smul] at h; exact h )
 have H := contraction (u:=Ux) (x:=y) (A:=A) (v:=y) hx; rw [ hD,sub_self ] at H; apply G.colorMat_injective; rw [ map_zero ]; let m:= Γ (axis V y y); change m= 0; have hm: m * U (Ux y)=0:=H; rw [ ← mul_one m, ← G.mat_mul_star (Ux y), ← mul_assoc, hm, zero_mul ]
end YM.FVA2.Gen
