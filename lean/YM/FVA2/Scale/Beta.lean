import YM.FVA2.Scale.Homogeneous
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Analysis.Calculus.Deriv.Polynomial
/-!
# Scale differentiation at every fixed order: actual conversion of beta

This is a formula on the unique group action **on these correlations**.
Not a computation of coefficient `b0` nor asserting an `O(g³)` beta theorem
(latter may use higher parity inputs & separate first-difference calculation).
Includes scale ODE of manuscript with same argument; INSIDE the formal algebra.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Scale.Beta
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical
open Dframe Level Reg.Point Reg.Token Reg.Unique Reg.Choice Facets Equator Measure Jury
open Meter GroupS
variable {G:Gauge}
def Roll (p:ℝ→Cn)(t:ℝ)(f:Cn): Prop:= ∀ n:ℕ,HasDerivAt ( fun t=> coeff n (p t) ) ( coeff n f ) t
namespace Roll
variable {p q:ℝ→Cn}{t:ℝ}{a b:Cn} (hp:Roll p t a)(hq:Roll q t b)
private lemma sumA {I:Type*}(s:Finset I)(a:I→ℝ→ℂ)(b:I→ℂ)(h:∀ i∈s,HasDerivAt (a i) (b i) t): HasDerivAt (fun t=> ∑ i∈s, a i t) (∑ i∈s,b i) t:= by rw [ ← show ( ∑ i∈s,a i )= (fun t=> ∑ i∈s,a i t) from funext (fun i=> Finset.sum_apply ..) ]; exact HasDerivAt.sum h
lemma yes (f:Cn)(t:ℝ): Roll (fun _=>f) t 0:= by intro i; rw [ map_zero ]; exact hasDerivAt_const ..
include hp
lemma single (h:Roll p t b): a=b:= PowerSeries.ext fun i=> HasDerivAt.unique ( hp i ) ( h i )
lemma symbol (h:∀ t,Rooted (p t)): Rooted a:= by have ht:= hp 0; have he: (fun t=> coeff 0 (p t))=(fun _=>0):= funext h; rw [he] at ht; exact ht.unique (hasDerivAt_const ..)
lemma pt_comp (s:Cn)(h:Rooted s): Roll (fun t=> ( p t ).subst s) t (a.subst s):= by intro i; simp_rw [← Constants.actual_subst _ _ h, coeff_mk,rules,smul_eq_mul ]; exact sumA (Finset.Iic i) _ _ ( fun j _=> ( hp j ).const_mul _ )
include hq
lemma link : Roll (fun t=> p t * q t) t (a*q t+p t*b):= by intro i; simp_rw [ map_add,coeff_mul, ← Finset.sum_add_distrib]; exact sumA _ _ _ ( fun j _=> (hp j.1).fun_mul (hq j.2) )
omit hq
local notation "r"=> p t
lemma valid (n:ℕ): Roll (fun i=> p i ^ n) t ( C (n:ℂ) * r^(n-1) * a ):= by
    induction n with
    | zero=> simp only [pow_zero, Nat.cast_zero,map_zero,zero_mul ]; exact yes _ _
    | succ n ih=>
       simp_rw [pow_succ (p _), Nat.add_one_sub_one]
       convert! ih.link hp using 1; -- simplify RHS
       push_cast; simp only [map_add,map_one]; cases n with
       | zero=> simp
       | succ n=> rw [ Nat.add_one_sub_one,pow_succ ]; ring -- parameter x
-- chain for q constant with substitution base value equal to X = variable. no convergence claim.
lemma main (f:Cn)(hx:∀ t,Rooted (p t))(ht:r=X): Roll (fun i=> f.subst (p i)) t ( (PowerSeries.derivative ℂ f) * a ):= by
    have hh:= hp.symbol hx; intro n; let B(k:ℕ):= C (k:ℂ)* r ^ (k-1)*a
    let J:= Finset.Iic n; let Hc(k:ℕ):= coeff k f; let A i t:= coeff n (p t ^ i) * Hc i; have he (t): coeff n ( f.subst (p t) )=∑ i∈J,A i t:= by rw [← Constants.actual_subst _ _ ( hx t ),coeff_mk,rules]; rfl
    have HK:= sumA J A (fun k:ℕ=> coeff n ( B k ) * Hc k ) (fun j _=> ( ( hp.valid j ) n ).mul_const (Hc j)); simp_rw [he]; convert HK using 1; -- differ factors
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (f:=fun i j=> coeff i (PowerSeries.derivative ℂ f)*coeff j a), Finset.sum_range_succ, Nat.sub_self, hh, mul_zero, add_zero ]; unfold J; rw [ ← Nat.range_succ_eq_Iic, Finset.sum_range_succ' ]; unfold B; simp only [ht,Nat.cast_zero,map_zero,zero_mul,add_zero,Nat.add_one_sub_one, coeff_derivative ]; refine Finset.sum_congr rfl (fun i hi=>?_ ); rw [mul_assoc (C _),coeff_C_mul, coeff_X_pow_mul',if_pos ( Nat.le_of_lt ( Finset.mem_range.mp hi ) ) ]; unfold Hc; push_cast; ring
end Roll
variable {G:Gauge}(p:ℝ→Cn)
abbrev beta : Cn:= mk (fun i=> deriv ( fun t=> coeff i ( p t ) ) 0 )
lemma origin (h:Clear p): Roll p 0 (beta p):= by
    intro i; rw [beta,coeff_mk]; apply DifferentiableAt.hasDerivAt; obtain ⟨Q,hQ⟩:= Rhythm.from_poly.mp ( Rhythm.unit.mpr (h i)); rw [hQ]; exact (Q.differentiable.restrictScalars ℝ).differentiableAt.comp _ (Complex.ofRealCLM.differentiableAt) -- deriv under definal
lemma running (A:Arenas G)(T:ℝ→Frames G)(H:Touched A p T) (h:Clear p) (t:ℝ): Roll p t ( (beta p).subst (p t) ):= by
    obtain hF:= ( origin p h ).pt_comp (p t) ( H.led t|>.start ); intro i; have ht := hasDerivAt_id' (𝕜:=ℝ) t; have hv := hF i; have hk: HasDerivAt (fun x:ℝ=> x-t) 1 t:= ht.sub_const t; rw [ ← sub_self t ] at hv -- dangerous p t inside? only 0 appears beta reducible?
    obtain hx:= HasDerivAt.scomp (h:=fun x:ℝ=> x-t) t hv hk; rw [one_smul] at hx; apply hx.congr_of_eventuallyEq; filter_upwards with x; exact congr_arg (fun z=> coeff i z) ( ( congr_arg p ( add_sub_cancel t x ) ).symm.trans ( H.additive t (x-t)|>.1 ))
lemma warp (A:Arenas G)(T:ℝ→Frames G)(H:Touched A p T) (h:Clear p): Rooted ( beta p ) ∧ coeff 1 (beta p)=0:= by refine ⟨ ( origin p h ).symbol ( fun t=> H.led t |>.start ), ?_ ⟩; obtain ht:= origin p h 1; simp_rw [ Tangent.lead ( H.led _ ) ] at ht; exact ht.unique (hasDerivAt_const ..) -- Real β next
variable (ν:ℝ)(Y: Initialize G){V: Normalize.Store G}(K:Rose.Pick V){O: Booked (Press.portDeck G)}(T:MS_Data G O)
variable (S:Prescription (Press.portDeck G)) (h:G.Simple)(hs:TaylorOKF T (Press.wickInput Y) S)(hr:Favors.Horder S)(hu:Ace.UnitP S)
local notation "φ"=> Measure.f K ν T
local notation "χ"=> GroupS.ψ K T ν
local notation "ξ"=> GroupS.Ψ K T ν
include h hs hr hu
-- The formal beta functions are related by the derivative of the coupling conversion.
theorem translated : (beta ξ).subst ( Measure.f K ν T ) = PowerSeries.derivative ℂ φ * beta χ:= by
    have hc:= ( origin ξ ( Precise.fitM ν Y K T S h hs hr hu ) ).pt_comp φ ( Specific.vigor_f Y K ν T S h hs hr hu|>.start ); refine hc.single ?_; rw [ show (fun t=> (ξ t).subst φ)=_ from funext ( fun i=> GroupS.contract0 ν Y K T S h hs hr hu i ) ]; exact (origin χ ( Precise.smooth ν Y K T S h hs hr hu ) ).main φ ( fun i=> ( GroupS.true_ψ ν Y K T S h hs hr hu i ).start ) (( GroupS.scaleN ν Y K T S h hs hr hu ).ground.1)
end YM.FVA2.Scale.Beta
