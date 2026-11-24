import YM.FVA2.Gen.World
/-! # Real gauge covariance at all orders -/
noncomputable section
set_option autoImplicit false
namespace YM.FVA2.Gen
open Function Finset Set Filter Topology
open scoped ContDiff BigOperators Classical Matrix.Norms.Frobenius
open Lattice RG Labels Precision
variable {E F R : Type*} [NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F][NormedRing R][NormedAlgebra ℝ R]
variable {G:Gauge}{A B:Sky G}{f:Mist G}{u:E4→ G.El}{x:E4}{v i j:Axis}
local notation "Cℓ"=>G.Color
local notation "M"=> G.Mat
local notation "Γ"=> G.colorMat
local notation "U"=> G.mat
local notation "T"=> E4
local notation "L"=>G.El
local notation "C'"=> Mist G
local notation "P"=> Sky G
local notation "l'"=> G.colorMat.toContinuousLinearMap
local notation "δ"=> par
local notation "Y"=> hat G
local notation "▶"=> Lived
-- algebraic universal lemmas. Maurer convention right-mult U.
section
omit [NormedAlgebra ℝ R]
variable {p r u a b c d A B C D K T' X F' : R}
-- D_i u = u A_i - Y_i u. a=δi U,b=δj; p=δi δj U; A (old i),B (old j). C,D new; c old i/j, d old j/i,K,T' new i/j,etc
-- CovCur = P K - ...
private lemma covalg (ha:a=u*A-C*u)(hb:b=u*B-D*u)(ht:K*u + D*a = a*B+u*c-p)(hf:T'*u+C*b=b*A+u*d-p): (K-T'+(C*D-D*C))*u=u*(c-d+(A*B-B*A)):=by
    rw [add_mul,sub_mul,sub_mul,show K*u=a*B+u*c-p-D*a from eq_sub_of_add_eq ht, show T'*u=b*A+u*d-p-C*b from eq_sub_of_add_eq hf, ha,hb,mul_assoc C D u,mul_assoc D C u]; noncomm_ring
private lemma deralg (ha:a=u*A-C*u)(ht:K*u=u*F')(hf:X*u + K*a=a*F'+u*c): (X+(C*K-K*C))*u=u*(c+(A*F'-F'*A)):=by
    rw [add_mul,sub_mul,show X*u=_ from eq_sub_of_add_eq hf,ha,mul_assoc C K u,ht]; -- remaining cancellation K*u*A
    rw [ mul_sub K,mul_assoc K, ← mul_assoc K u,ht ]; noncomm_ring
end
private lemma hat_c (hf:ContDiff ℝ ∞ f): ContDiff ℝ ∞ (Y f):= (l').contDiff.comp hf
private lemma sky_der (h:Lived u) : par (basis i) (U ∘ u) x= U (u x)*Y (A i) x - Y (skyturn u A i) x * U (u x):= by rw [skyline h]; abel
variable (hA:Fluid A)(hu:Lived u)
local notation "A'"=> skyturn u A
local notation "Λ"=> U∘ u
include hA hu
private lemma sky_derive : par (basis i) (Y (A' j)) x * U (u x) + Y (A' j) x * par (basis i) Λ x = par (basis i) Λ x * Y (A j) x + U (u x) * par (basis i) (Y (A j)) x - par (basis i) (par (basis j) Λ ) x:= by
    have hf : ContDiff ℝ ∞ ( Y (A' j) ):= hat_c ( skyline_sm hu hA j ); have hk := hat_c ( hA j ); have hv: Y (A' j) * Λ = Λ * Y ( A j ) - par (basis j) Λ:= funext fun x=> skyline hu
    have hp:= congrArg (fun f:E4→M=> par (basis i) f x) hv
    -- normalization may fight instances Mat.Apply generic par operation; dsimp only
    change par _ ( Y (A' j) * Λ ) x= par _ ( Λ * Y (A j)-_ ) x at hp; rw [ par_mul (hf.differentiable (by simp) x) ( hu.differentiable (by simp) x ), par_sub ( f:=Λ * Y (A j) ) ( ((hu.mul hk).differentiable (by simp)) x ) (( sway hu ).differentiable (by simp) x), par_mul ( hu.differentiable (by simp) x ) ( hk.differentiable (by simp) x ) ] at hp; dsimp only [comp_apply] at hp; rw [add_comm, add_comm ( par _ Λ _ * _ )]; exact hp
omit hA hu
private lemma byR (g:G.El){A B:G.Mat}(h:A*U g=B*U g): A=B:= by rw [ ← mul_one A,← mul_one B, ← G.mat_mul_star g, ← mul_assoc, ← mul_assoc, h ]
include hA hu
theorem skyCur (i j:Axis): surf A' i j=fantasy u (surf A i j):= by
    funext x; apply G.colorMat_injective; apply byR (u x); change Y (surf A' i j) x * _= Y (fantasy u (surf A i j)) x * _; rw [umbrella,matS hA,matS (skyline_sm hu hA)]; apply covalg (sky_der hu) (sky_der hu) ( sky_derive hA hu ); rw [ par_swap hu ]; exact sky_derive hA hu
variable {hf:ContDiff ℝ ∞ f}
omit hA
private lemma skyslot (hf:ContDiff ℝ ∞ f) : par (basis i) (Y (fantasy u f)) x * U (u x)+Y (fantasy u f) x * par (basis i) Λ x= par (basis i) Λ x* Y f x + U (u x)* par (basis i) (Y f) x:= by
    have hs := hat_c ( imagineC hu hf ); have ht:= hat_c hf; have he: Y (fantasy u f) * Λ= Λ * Y f:= funext fun x=> umbrella u f; have hp := congrArg (fun f:E4→ M=> par (basis i) f x) he; rw [par_mul ( hs.differentiable (by simp) x ) ( hu.differentiable (by simp) x ),par_mul ( hu.differentiable (by simp) x ) (ht.differentiable (by simp) x)] at hp; rw [add_comm,add_comm (par _ Λ _*_)]; exact hp
theorem skyN (hf:ContDiff ℝ ∞ f)(i:Axis): deriveN A' (fantasy u f) i=fantasy u (deriveN A f i):= by
    funext x; apply G.colorMat_injective; apply byR (u x); change Y (deriveN A' _ i) x * _= Y (fantasy u _) x * _; rw [umbrella,matD hf,matD ( imagineC hu hf )]; exact deralg (sky_der hu) (umbrella u _) (skyslot hu hf) -- hA unused?
end YM.FVA2.Gen
