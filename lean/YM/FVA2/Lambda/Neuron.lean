import YM.FVA2.Lambda.Rate
/-!
# Gaussian moments νa(q)=exp(-(1+a)Z)

 IBP whole line and finrank product. Basic radial-powers recurrence for later integrability & timing. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Lambda.Gaussian
open Function Filter Set Finset MeasureTheory Real Metric Lattice
open MS MS.Plane MS.Momentum MS.Arts MS.Koszul MS.Landau MS.Landau.Detect
open MS.Wind MS.Wind.Modeled MS.Heat MS.Heat.Signal MS.High MS.Tone MS.Tone.Frame MS.Color MS.Native
open MS.Book MS.Book.Convolve MS.Dock MS.Emit MS.Pearl
open MS.City MS.Plane.Flux
open Area Shells Pages
open Lathe (γ)
open Complex (I)
open scoped Topology ContDiff BigOperators Classical InnerProductSpace ENNReal NNReal
variable {G:Gauge}{a:ℝ}
local notation "Z"=> Momentum.sq (A:=Axis)
variable (ha:0≤a)(n k:ℕ)(q:QP)
def N (a x:ℝ):= exp (-(1+a)*x^2)
abbrev nu (a:ℝ)(n:ℕ)(x:ℝ):= x^n*N a x
def pin (a:ℝ)(n:ℕ):ℝ:=∫ x:ℝ, nu a n x
include ha
lemma nut : Integrable (nu a n):= by obtain he:= integrable_rpow_mul_exp_neg_mul_sq (show (0:ℝ)<1+a from by linarith) (show (-1:ℝ)<(n:ℝ) from lt_of_lt_of_le (by norm_num : (-1:ℝ)<0) (by positivity)); simp_rw [Real.rpow_natCast] at he; exact he
omit ha in
lemma pin₀ : pin a 0=√(π/(1+a)):= by unfold pin; simp only [ nu,N, pow_zero,one_mul ]; rw [integral_gaussian] -- not positive? used? h
lemma nextPin : pin a (n+2)=( (n+1:ℕ):ℝ )/(2*(1+a)) * pin a n:= by
    let h:=(1+a); let r(x:ℝ):= (↑(n+1:ℕ):ℝ)*nu a n x-2*h*nu a (n+2) x
    have hi : ∀ x:ℝ, HasDerivAt (nu a (n+1)) (r x) x:= by
       intro x; let p:= hasDerivAt_id' x; have hx:= ( p.pow (n+1) ).fun_mul ( ( ( p.pow 2 ).const_mul (-h) ).exp ); convert! hx using 1; unfold r h nu N; simp only [Pi.pow_apply ]; push_cast; simp only [pow_add]; ring
    have h0:Integrable r:= ( (nut ha n).const_mul (↑(n+1:ℕ):ℝ) ).sub ( (nut ha (n+2)).const_mul (2*h) ); obtain hp:= integral_eq_zero_of_hasDerivAt_of_integrable hi h0 (nut ha (n+1)); unfold r at hp; rw [integral_sub ((nut ha n).const_mul _) ((nut ha (n+2)).const_mul _), integral_const_mul, integral_const_mul] at hp; apply Eq.symm; rw [div_mul_eq_mul_div,div_eq_iff (by positivity)]; exact (sub_eq_zero.mp hp).trans (mul_comm ..)
omit ha
abbrev ar (α:Axis→ℕ)(q:QP):ℝ:= ∏ i:Axis,( q i )^(α i)
def capμ:ℝ:= ((2*π)^ (4:ℕ))⁻¹
def rock (α:Axis→ℕ)(a:ℝ)(n:ℕ)(q:QP):=ar α q * ( Z q )^n * ( γ a q )
def tide (α:Axis→ℕ)(a:ℝ)(n:ℕ):ℝ:=∫ q:QP, rock α a n q∂μq
variable (α: Axis→ℕ)
lemma venue (q:QP)(a:ℝ): rock α a 0 q=∏ i:Axis, nu a (α i) (q i):= by unfold rock ar nu N γ; simp_rw [ Finset.prod_mul_distrib, ← Real.exp_sum,Momentum.sq, Finset.mul_sum,pow_zero,mul_one ] -- name.Exp sum
lemma land : μq=( ENNReal.ofReal capμ ) • ( volume : Measure QP ):= by simp only [μq,covMeasure, Axis,Fintype.card_fin, capμ]; -- check parse
include ha
lemma rustic0 : Integrable ( rock α a 0 ) μq:= by
    rw [ show rock α a 0=fun q=>∏ i:Axis,nu a (α i) (q i) from funext (fun q=> venue α q a ), land ]; exact Integrable.smul_measure ( Integrable.fintype_prod (μ:=fun i:Axis=> volume) ( fun i=> nut ha (α i) ) ) ( ENNReal.ofReal_ne_top )
omit ha in
lemma base0 : tide α a 0=capμ*∏ i:Axis,pin a (α i):= by
    unfold tide; simp_rw [ venue ]; rw [ land, integral_smul_measure, ENNReal.toReal_ofReal (by unfold capμ; positivity), smul_eq_mul ]; congr; exact integral_fintype_prod_volume_eq_prod _ -- maybe no goals
omit ha
abbrev shift (α:Axis→ℕ)(c:Axis):Axis→ℕ:= fun i=> if i=c then α i+2 else α i
lemma slotR (f:Axis→ℝ)(c:Axis)(x:ℝ): (∏ i:Axis,if i=c then f i*x else f i)= (∏ i:Axis, f i)*x:= by
    have he : (∏ i:Axis,if i=c then f i*x else f i)=∏ i:Axis,f i*(if i=c then x else 1):= Finset.prod_congr rfl fun i _=> by split <;> simp [*]
    rw [he, Finset.prod_mul_distrib]; simp
lemma crop (c:Axis): ar (shift α c) q=ar α q*(q c)^2:= by
    rw [ar]; have hx(i:Axis): q i ^(shift α c i)= if i=c then q i^ (α i)*(q c)^2 else q i^(α i):= by unfold shift; split_ifs <;> first| rfl | (simp [*,pow_add])
    simp_rw [hx]; exact slotR ..
lemma horizon (a:ℝ): rock α a (n+1) q= ∑ c:Axis, rock ( shift α c ) a n q:= by
    unfold rock; simp only [ crop ]; rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum, pow_succ,show ∑ c:Axis,q c ^ (2:ℕ)=Z q from rfl ]; ring
end YM.FVA2.Lambda.Gaussian
