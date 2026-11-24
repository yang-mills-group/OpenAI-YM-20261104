import YM.Integration.WilsonSeparatedOriginalProfileParents

/-! Period- and cutoff-independent total price of the original signed physical source. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonSeparatedOriginalProfileTariff
open Finset Wilson Lattice RG05Readout RG05Readout.Pulse RG05Readout.Native
open WilsonSeparatedOriginalPairedFolio
open scoped Classical BigOperators
variable {G:Gauge} (C:Family G)(s:Fin 3→ℕ)

def scale (n:ℕ)(r:ℝ):ℝ:=∏i:Fin 3,(C.S.a n/r)^4*(C.S.a 0/C.S.a n)^(s i)

def budget (n rank:ℕ)(r η X cap:ℝ)(g:Body):ℝ:=max 1 (scale C s n r*((((Lattice.box ⌈cap+2⌉₊).card:ℝ)^3)*
  (mass g*abs (earn s C n rank η r*X))))

private theorem leg (m n d:ℕ){r:ℝ}(rp:0<r):‖(r:ℂ)⁻¹^4*gate C m n d‖=(C.S.a n/r)^4*(C.S.a m/C.S.a n)^d:=by
  unfold gate
  simp only [norm_mul,norm_pow,norm_inv,norm_div,Complex.norm_real,Real.norm_of_nonneg (C.S.a_pos n).le,
    Real.norm_of_nonneg (C.S.a_pos m).le,Real.norm_of_nonneg rp.le]
  rw [div_pow,div_eq_mul_inv,inv_pow];ring

theorem all_dates (m n:ℕ){r:ℝ}(rp:0<r):‖premiums C s m n r‖ ≤ scale C s n r:=by
  unfold premiums scale;rw [norm_prod];apply prod_le_prod
  · intro i _;exact norm_nonneg _
  · intro i _;rw [leg C m n (s i) rp];apply mul_le_mul_of_nonneg_left _ (pow_nonneg (div_nonneg (C.S.a_pos n).le rp.le) _)
    exact pow_le_pow_left₀ (div_nonneg (C.S.a_pos m).le (C.S.a_pos n).le) (div_le_div_of_nonneg_right (C.S.strictAnti.antitone (Nat.zero_le m)) (C.S.a_pos n).le) _

theorem reporting {m n:ℕ}(nm:n ≤ m){r:ℝ}(rp:0<r):‖premiums C s m n r‖ ≤ (C.S.a n/r)^12:=by
  unfold premiums;rw [norm_prod]
  calc
    _ ≤ ∏_i:Fin 3,(C.S.a n/r)^4:=by
      apply prod_le_prod (fun _ _=>norm_nonneg _);intro i _;rw [leg C m n (s i) rp]
      apply mul_le_of_le_one_right (pow_nonneg (div_nonneg (C.S.a_pos n).le rp.le) _)
      exact pow_le_one₀ (div_nonneg (C.S.a_pos m).le (C.S.a_pos n).le) ((div_le_one (C.S.a_pos n)).2 (C.S.strictAnti.antitone nm))
    _=_:=by simp only [prod_const,card_univ,Fintype.card_fin,←pow_mul]

theorem available (n rank:ℕ)(r η X cap:ℝ)(g:Body):1 ≤ budget C s n rank r η X cap g:=le_max_left ..

theorem full (m n rank:ℕ){r:ℝ}(rp:0<r)(η X cap:ℝ)(g:Body){ε:ℝ}(ep:0 ≤ ε):
    ‖premiums C s m n r‖*((((Lattice.box ⌈cap+2⌉₊).card:ℝ)^3)*(mass g*abs (earn s C n rank η r*X)*ε)) ≤ 
    budget C s n rank r η X cap g*ε:=by
  let a:=(((Lattice.box ⌈cap+2⌉₊).card:ℝ)^3)*(mass g*abs (earn s C n rank η r*X))
  have a0:0 ≤ a:=mul_nonneg (by positivity) (mul_nonneg (positive g) (abs_nonneg _))
  calc
    _=(‖premiums C s m n r‖*a)*ε:=by unfold a;ring
    _ ≤ (scale C s n r*a)*ε:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (all_dates C s m n rp) a0) ep
    _ ≤ _:=mul_le_mul_of_nonneg_right (le_max_right ..) ep

end YM.Integration.WilsonSeparatedOriginalProfileTariff
