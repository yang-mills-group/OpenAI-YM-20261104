import YM.MSbar.Bristol.Rio
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Bristol
open Function Filter Precision Whisk Lis Cacao Push Uniform Lattice RG Tonic Aqua
open Gauge Midpoint Rolling Exterior Wilson Wave Lis Cypress
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure Work.G05 CrossH
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Bakery.Portal Further.GaussianScalar Jade Kelvin Bout Parma Tramp Heath Stock Heath.Cottage Film Lodge Measuring RawP
variable {G:Gauge}{c:Side}{σ:Type}[Fintype σ][DecidableEq σ]
variable {G:Gauge}{c:Side}{p q m:ℕ} (R:Rep G c)(Z:Nesting G c)(b:PowerSeries ℝ)
local notation "X₀"=>Positions (Primary c G)
local notation "X"=> Pot (Primary c G)
local notation "Ω"=>ink c R.clip R.path
local notation "V"=> PowerSeries ℝ
local notation "φ"=>film R Z
local notation "S"=> bley b Z Ω
variable (u r s:ℝ)
local notation "μ"=>PowerSeries.coeff
variable (hp:s/u=r)(hv:0<u)(hr:u*r=s)(h:Kind Z)(ht:Expanse Z 1 p) (hR:Premier (Rolling.main c R.clip R.path))
noncomputable def Yturn (u:ℝ) : X₀ →L[ℝ] X₀ := u • ContinuousLinearMap.id ..
local notation "θ"=> homogeneousComponent
noncomputable def pegsK (b:PowerSeries ℝ)(s u:ℝ)(p i j:ℕ):= s^i*(u^j*u⁻¹^i-taste (p-i) (b^j*b⁻¹^i) s)
noncomputable def lampZ (Z:Nesting G c)(b:PowerSeries ℝ)(s u:ℝ)(p:ℕ) (i:ℕ):= ∑ j∈range (i+2+1),pegsK b s u p i j • homogeneousComponent j (PowerSeries.coeff i Z)
noncomputable def pegs (Z:Nesting G c)(b:PowerSeries ℝ)(s u:ℝ)(p:ℕ): Pot (Primary c G):=∑ i∈range (p+1), lampZ Z b s u p i
noncomputable def surf (f:PowerSeries ℝ)(s u:ℝ)(p:ℕ):= taste p (f^2) s -u^2
include hp hv hr h ht hR
lemma slips : film R (bley b Z (ink c R.clip R.path)) s p = (film R Z r p ∘ Yturn u)+clue (pegs Z b s u p)+surf b s u p • clue (ink c R.clip R.path):=by
    let L:=@Yturn G c u; let P:= priceS p r R (tariff c p R.clip R.path Z)
    have hb(x:Positions (Primary c G))(y:ℝ)(N:Nesting G c): eval x (priceS p y R N)=taste p (picture x N) y:=by unfold priceS taste picture; rw [_root_.map_sum]; simp_rw [PowerSeries.coeff_map,← C_mul',map_mul,eval_C]; -- exact
    have he(x:X₀): eval (u • x) (ink c R.clip R.path)= u^2*MvPolynomial.eval x Ω:=by unfold ink; rw [pots,pots,Tensor.homogeneous];rfl -- name
    let T:= ticket b Z
    have ht'(x:X₀): taste p (picture x (tariff c p R.clip R.path S)) s=taste p (picture x T) s- taste p (b^2) s* eval x (ink c R.clip R.path):=by
         unfold taste picture tariff bley; rw [sum_mul,←sum_sub_distrib]; apply sum_congr rfl; intro i hi; rw [PowerSeries.coeff_map,PowerSeries.coeff_map,map_sub,map_sub,map_sub,map_sub,PowerSeries.coeff_mk,←C_mul',_root_.map_mul,MvPolynomial.eval_C,map_sub]; unfold T; by_cases hv:i=0; · subst i; simp; ring
         simp only [PowerSeries.coeff_one, if_neg hv,PowerSeries.coeff_C_of_ne_zero hv,map_zero, sub_zero]; ring -- check
    have hP(x:X₀):taste p (picture x (tariff c p R.clip R.path Z)) r=taste p (picture x Z) r-eval x Ω:=by
         unfold tariff picture taste; simp only [PowerSeries.coeff_map,map_sub,mul_sub, sum_sub_distrib]; rw [sub_right_inj,Finset.sum_eq_single_of_mem (f:=fun i=>r^i*(MvPolynomial.eval x) (μ i (PowerSeries.C Ω))) 0 (mem_range.mpr (Nat.zero_lt_succ p))]; · simp
         exact fun j _ hj=>by simp [PowerSeries.coeff_C_of_ne_zero hj]
    let iP:=pegs Z b s u p; have hB(x:X₀): taste p (picture (u • x) Z) r -taste p (picture x (ticket b Z)) s=clue iP x:=by
         unfold iP pegs clue; rw [tasteCut,taste,_root_.map_sum,←Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro i hi; have hL:= buys (i+2) (μ i Z) (by simpa only [one_mul] using ht.profile _ (Nat.lt_succ_iff.mp (mem_range.mp hi))); unfold picture lampZ; rw [PowerSeries.coeff_map]
         nth_rw 1 [← hL]; rw [map_sum,map_sum,mul_sum,mul_sum,←sum_sub_distrib]; apply sum_congr rfl; intro j hj
         unfold pegsK; rw [hene u 0 x j _,← C_mul',_root_.map_mul,MvPolynomial.eval_C,← hp]; ring
    funext x; have hz: r • (u • x)=s • x:=by rw [smul_smul,mul_comm,hr]
    unfold film; rw [pricesP,pricesP]; change walnut _ _-MvPolynomial.eval x (priceS p s R _)= (walnut R (r • u • x)-MvPolynomial.eval (u • x) (priceS p r R _))+_+_; rw [hz,hb (u•x) r,hb x s,hP,ht',he,← hB x]; change _= _+surf b s u p*eval x Ω; unfold surf T; ring
end YM.MSbar.Bristol
