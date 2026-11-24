import YM.Integration.WilsonMeasuredPublicEntranceOwnerOptical

/-! A finite before-period log bound for each earned amount buys the exact
post-crop optical wage, even when a returned trial has very small widths. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceReserveWallet
open Finset Marker QuadraticLocal WilsonThermometerMixedCollarSubpower
open WilsonMeasuredPublicEntranceOwnerWallet
open scoped Classical BigOperators
variable {V:Type}[DecidableEq V]{marks:Census V}

theorem funded (H:ℝ)(hH:1≤H)(a n:ℕ)(size:∀s:marks.Mode,s.val.card≤n)
    (w:V→ℝ)(wp:∀i,0<w i)(owner:V)(C M U:ℝ)(up:0≤U)
    (width:∀i,(w i)⁻¹ ≤ Real.exp U)(soft:C≤Real.exp U)(hard:2*(w owner*M)≤Real.exp U)
    (s:marks.Mode):
    let reserve:=Nat.ceil (2*U)
    let wage:=Stoop.radius w (divisor w owner C M)
    1 ≤ H^a*(Real.exp (n*(reserve:ℝ)*(scale H)^3)*Poly.toll wage s):=by
  intro reserve wage
  have zp:1 ≤ scale H:=by dsimp [scale];linarith only [le_max_left 0 (Real.log (Real.log H))]
  have sale:divisor w owner C M ≤ Real.exp U:=
    max_le (max_le (Real.one_le_exp_iff.mpr up) soft) hard
  have r0:0<(divisor w owner C M):=(zero_lt_one.trans_le (le_trans (le_max_left _ _) (le_max_left _ _)))
  have two:2*U≤(reserve:ℝ):=Nat.le_ceil _
  have pw u:0<wage u:=div_pos (wp u) r0
  have each (u:V):1≤Real.exp (reserve:ℝ)*wage u:=by
    have raw:(wage u)⁻¹≤Real.exp (reserve:ℝ):=by
      calc
        _=(divisor w owner C M)*(w u)⁻¹:=by dsimp [wage,Stoop.radius];rw [inv_div,div_eq_mul_inv]
        _≤Real.exp U*Real.exp U:=mul_le_mul sale (width u) (inv_nonneg.mpr (wp u).le) (Real.exp_nonneg _)
        _=Real.exp (2*U):=by rw [←Real.exp_add];congr 1;ring
        _≤_:=Real.exp_le_exp.mpr two
    have paid:=mul_le_mul_of_nonneg_right raw (pw u).le
    simpa only [inv_mul_cancel₀ (pw u).ne'] using paid
  have product:1 ≤ (Real.exp (reserve:ℝ))^s.val.card*Poly.toll wage s:=by
    calc
      _=∏_u∈s.val,(1:ℝ):=by simp
      _≤∏u∈s.val,(Real.exp (reserve:ℝ)*wage u):=Finset.prod_le_prod (fun _ _=>zero_le_one) (fun u _=>each u)
      _=_:=by rw [Finset.prod_mul_distrib,Finset.prod_const];rfl
  have fraction:(Real.exp (reserve:ℝ))^s.val.card≤Real.exp (n*(reserve:ℝ)*(scale H)^3):=by
    rw [←Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    calc
      _≤(n:ℝ)*reserve:=by gcongr;exact size s
      _≤_:=le_mul_of_one_le_right (by positivity) (one_le_pow₀ zp)
  have normalized:=product.trans (mul_le_mul_of_nonneg_right fraction (Poly.worth pw s).le)
  exact normalized.trans (le_mul_of_one_le_left (normalized.trans' zero_le_one) (one_le_pow₀ hH))

theorem calendar {H U C D₀:ℝ}(hp:1≤H)(up:0≤U){f b d:ℕ}
    (cash:U≤C*(1+Real.log H)^d)(way:((f+1-b:ℕ):ℝ)≤D₀*(1+Real.log H)^d):
    ((f+1-b+Nat.ceil (2*U):ℕ):ℝ)≤(D₀+2*C+1)*(1+Real.log H)^d:=by
  have next:(Nat.ceil (2*U):ℝ)<2*U+1:=Nat.ceil_lt_add_one (by positivity)
  have phase:1≤(1+Real.log H)^d:=one_le_pow₀ (by linarith only [Real.log_nonneg hp])
  push_cast
  linarith only [way,cash,next,phase]

end YM.Integration.WilsonMeasuredPublicEntranceReserveWallet
end
