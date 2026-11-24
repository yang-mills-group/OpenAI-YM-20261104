import YM.FVA2.Gen.Dome
import YM.Maxwell.Exterior
/-! # Covariant curvature radial-case Jrad formulas, no interactions ignored -/
noncomputable section
set_option autoImplicit false
namespace YM.FVA2.Gen
open Function Set Filter Finset MeasureTheory Topology
open scoped ContDiff BigOperators Classical Matrix.Norms.Frobenius
open Maxwell Labels Precision Lattice RG
variable {G:Gauge}{A: Sky G}{f:Mist G}{u:E4→G.El}{x:E4}{i j:Axis}
local notation "P"=> E4
local notation "C"=> G.Color
local notation "U"=> G.mat
local notation "δ"=> par
local notation "∇"=> deriveN
local notation "X'"=> ( skyturn u A )
def gleam (A:Sky G) (x:E4)(i j:Axis):ℕ→ Mist G
 | 0=> surf A i j
 | n+1=> ∑ k:Axis,x k • ∇ A ( gleam A x i j n ) k
variable (h:Fluid A)
include h
lemma gleam_c (n:ℕ): ContDiff ℝ ∞ (gleam A x i j n):=by
    induction n with | zero=> exact cSurf h ..| succ n ih=> rw [gleam,sum_fn]; refine ContDiff.sum (fun i _=> ContDiff.const_smul ( x i ) ( cDer h ih _ ) )
lemma gleam_f (hu:Lived u)(n:ℕ): gleam X' x i j n = fantasy u (gleam A x i j n):=by
    induction n with| zero=> exact skyCur h hu _ _| succ n ih=> rw [gleam,gleam]; simp_rw [ ih, skyN hu (gleam_c h _) ]; funext l; unfold fantasy; rw [Finset.sum_apply,Finset.sum_apply,map_sum]; exact Finset.sum_congr rfl (fun k _=> (map_smul ( G.adjoint (u l) ) (x k) ( deriveN A (gleam A x i j n) k l )).symm)
lemma par_radial : par (basis i) (fun y:E4=> axis A y y) x= A i x + ∑ j:Axis, x j • par (basis i) ( A j ) x:= by
    let F(j:Axis):= A j; have ht(j:Axis): HasFDerivAt (fun y:E4=> y j) (compAxis j) x := ( compAxis j ).hasFDerivAt; have H(k):= (ht k).smul ( h k|>.differentiable (by simp) x ).hasFDerivAt; obtain he:= (HasFDerivAt.fun_sum (u:=Finset.univ) (fun k _=> H k ) ).fderiv
    change fderiv ℝ (fun y:E4=> axis A y y) x=_ at he; unfold par; rw [he,_root_.sum_apply]; simp only [ _root_.add_apply, ContinuousLinearMap.smulRight_apply, _root_.smul_apply ]; change (∑ k:Axis, ( x k • δ (basis i) (A k) x + (basis i k) • A k x ))= _; simp [Finset.sum_add_distrib,ite_smul,add_comm, par]
variable (hp:Silent A)
include hp
lemma null_near (x:E4) (i:Axis): ∑ j:Axis,x j • par (basis i) (A j) x = -A i x:= by
    have he:= par_radial (x:=x) (i:=i) h; rw [ show (fun y:P=> axis A y y)=(fun y:P=> (0:C)) from funext hp ] at he; change ( fderiv ℝ (fun _:P=>(0:C)) _ ) _ = _ at he; rw [ fderiv_const_apply ] at he; simp only [_root_.zero_apply] at he; exact (neg_eq_of_add_eq_zero_right he.symm).symm -- check name
lemma null_centre (i:Axis): A i 0=0:= by have he := null_near h hp 0 i; simpa using he -- neg zero orientation
lemma ray_quiet (x:E4)(t:ℝ): axis A x (t • x)=0:=by
    by_cases he:t=0; · simp [he,axis,null_centre h hp]
    exact (smul_eq_zero.mp ((axis_scale t).symm.trans (hp (t • x)))).resolve_left he
lemma ray_der {f:Mist G} (x:E4)(t:ℝ): ∑ k:Axis,x k • deriveN A f k (t • x)= δ x f (t • x):= by
    let y:=t • x; have he:∑ k:Axis,x k • δ (basis k) f y= δ x f y:= by
       let D:=fderiv ℝ f y; change ∑ k:Axis,x k • D (basis k)=D x; conv_rhs=> rhs; rw [← show ∑ k:Axis,x k • basis k=x from (by ext i; simp) ]; --
       rw [map_sum]; exact Finset.sum_congr rfl (fun k _=> (map_smul D ..).symm)
    let X:=G.ad.flip (f y); unfold deriveN; simp_rw [smul_add, Finset.sum_add_distrib]; change (∑ k:Axis,x k • δ (basis k) f y) + (∑ k:Axis,x k • X ( A k y )) = _; rw [ he, ← show X (axis A x y)=(∑ k:Axis,x k • X ( A k y )) from ?_, show axis A x y=0 from ray_quiet h hp x t,map_zero,add_zero ]; unfold axis; rw [map_sum]; exact sum_congr rfl (fun k _=> map_smul X .. )
-- core. t factor
private lemma coreRay (x:E4)(t:ℝ)(j:Axis): t • (∑ i:Axis,x i • surf A i j ( t • x )) = t • par x (A j) (t • x) + A j (t • x):=by
    simp_rw [surf,smul_sub, Finset.sum_sub_distrib,ray_der h hp, smul_sub]; simp_rw [Finset.smul_sum,smul_smul]; have he:=null_near h hp (t • x) j; simp only [PiLp.smul_apply, smul_eq_mul] at he; rw [ he, sub_neg_eq_add ]
lemma jet_rose (x:E4)(i j:Axis)(n:ℕ)(t:ℝ): gleam A x i j n (t • x)= iteratedDeriv n (fun t:ℝ=> surf A i j ( t • x )) t:=by
    induction n generalizing t with
    | zero=> simp only [gleam,iteratedDeriv_zero]
    | succ n ih=>
        rw [gleam,Finset.sum_apply]; simp_rw [Pi.smul_apply]; rw [ray_der h hp,iteratedDeriv_succ,←funext ih ]; refine (( show HasDerivAt (fun t:ℝ=> gleam A x i j n (t • x)) ( par x (gleam A x i j n) (t • x) ) t from ?_ ).deriv).symm; simpa only [ zero_add ] using par_line ( ( gleam_c (x:=x) (i:=i) (j:=j) h n ).differentiable (by simp) ) x 0 t
-- inclusive Taylor
lemma eq_Jrad (x:E4)(i:Axis)(n:ℕ): ((n+1).factorial:ℝ)⁻¹ • iteratedDeriv (n+1) (fun t:ℝ=> A i (t • x)) 0= (( (n:ℝ)+2 )*( n.factorial:ℝ ))⁻¹ • ∑ j:Axis,x j • gleam A x j i n 0:= by
    let f(t:ℝ):= A i (t • x); let S(t:ℝ):= par x ( A i ) (t • x); let p(t:ℝ):= ∑ j:Axis,x j • surf A j i ( t • x ); have ht: ContDiff ℝ ∞ (fun t:ℝ=> t • x):= contDiff_id.smul contDiff_const; have hf: ContDiff ℝ ∞ f:= ( h i ).comp ht; have hs:ContDiff ℝ ∞ S:= ( sway ( h i ) ).comp ht; have hu: ContDiff ℝ ∞ p:= ContDiff.sum (fun j _=> (( cSurf h j i ).comp ht).const_smul (x j) )
    have H : (fun t:ℝ=> t • p t)=(fun t:ℝ=> t • S t ) + f:= funext fun t=> coreRay h hp x t i

    obtain hp' : iteratedDeriv n p 0= ∑ j:Axis, x j • gleam A x j i n 0 := by unfold p; rw [ iteratedDeriv_fun_sum (f:=fun j:Axis=> fun t:ℝ=> x j • surf A j i (t • x)) (fun j _=> ContDiffAt.const_smul ( x j ) ( (( cSurf h j i ).comp ht).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top) ) ) ]; apply Finset.sum_congr rfl; intro j _; rw [ iteratedDeriv_fun_const_smul_field ]; congr 1; simpa using ( jet_rose h hp x j i n 0 ).symm
    have hh := congrArg (fun p:ℝ→C=> iteratedDeriv (n+1) p 0 ) H; have hg : deriv f=S:= funext fun t=> by simpa only [ zero_add ] using (par_line ( ( h i ).differentiable (by simp) ) x 0 t ).deriv
    rw [ iteratedDeriv_add (f:=fun t:ℝ=> t • S t) (( contDiff_id.smul hs ).contDiffAt.of_le ( WithTop.coe_le_coe.mpr le_top )) ( hf.contDiffAt.of_le ( WithTop.coe_le_coe.mpr le_top )), iter_weight hu.contDiffAt, iter_weight hs.contDiffAt,hp', ← hg, ← iteratedDeriv_succ'] at hh; -- algebraic divisions explicitly nonzero
    let q:= iteratedDeriv (n+1) f 0; let A':= n.factorial; let r:ℝ:= n+1; let u:ℝ:=n+2; let B:=∑ j:Axis,x j • gleam A x j i n 0; have hr:u=r+1:= by unfold r u; ring
    have he₁:r ≠ 0:= by unfold r; positivity
    have he₂:u ≠ 0:= by unfold u; positivity
    have he₃:(A':ℝ)≠0:= (by unfold A'; positivity)
    rw [ Nat.factorial_succ, Nat.cast_mul, Nat.cast_add_one ]; change (r * A')⁻¹ • q=(u*A')⁻¹ • B
    apply smul_right_injective G.Color (show r * u * ( A':ℝ )≠0 from mul_ne_zero (mul_ne_zero he₁ he₂) he₃); simp_rw [smul_smul]; push_cast at hh; rw [show r*u*A'*(r*A')⁻¹=u from (by field_simp), show r*u*A'*(u*A')⁻¹=r from (by field_simp), hr, add_smul,one_smul ]; exact hh.symm
end YM.FVA2.Gen
