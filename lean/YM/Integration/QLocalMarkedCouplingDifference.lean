import YM.Integration.ActualPacketFiniteCopies
import YM.IterationFour.Running
import YM.Extra.MULTISOURCE_TRAJECTORIES.Algebra

/-! The exact all-mode difference between two scalar readings of one genuine
physical Laurent packet. Every original support, independent variable and
thermal spectator retains its own charged position. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalMarkedCouplingDifference

open Lattice Wilson RG Marker Precision LocalComparison ActualPacketFiniteCopies
open Comparison.Density.RenderM
open scoped Classical BigOperators

/-- Uniform local price for every signed original Laurent power allowed by the real bank. -/
def rate (k:ℕ) : ℝ :=
  ∑ e ∈ Finset.Icc (-(k:ℤ)) (k:ℤ), IterationFour.Currency.tiltFee (e:ℝ)

theorem rate_nonnegative (k:ℕ) : 0≤rate k :=
  Finset.sum_nonneg (fun _ _=>IterationFour.Currency.tiltFee_nonneg _)

theorem rate_mono {k l:ℕ} (h:k≤l) : rate k≤rate l := by
  unfold rate
  apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun (e:ℤ) _ _=>IterationFour.Currency.tiltFee_nonneg (e:ℝ))
  intro e he
  simp only [Finset.mem_Icc] at he ⊢
  omega

theorem scalar {β x y:ℝ} (hβ:0<β) (hx:x∈IterationFour.Currency.stripe β)
    (hy:y∈IterationFour.Currency.stripe β) (k:ℕ) (e:ℤ) (he:|e|≤(k:ℤ)) :
    let f:=IterationFour.Currency.gain
    ‖(((f x/f β:ℝ):ℂ)^e)-(((f y/f β:ℝ):ℂ)^e)‖≤rate k*β⁻¹*|x-y| := by
  let f:=IterationFour.Currency.gain
  have hg:0<f β:=inv_pos.mpr (Real.sqrt_pos.mpr hβ)
  have hp:0<(f β)^e:=zpow_pos hg _
  have money:=IterationFour.Currency.gain_compare (e:ℝ) hβ hx hy
  simp only [Real.rpow_intCast] at money
  have enter:e∈Finset.Icc (-(k:ℤ)) (k:ℤ):=Finset.mem_Icc.mpr (abs_le.mp he)
  have card:IterationFour.Currency.tiltFee (e:ℝ)≤rate k:=
    Finset.single_le_sum (f:=fun e:ℤ=>IterationFour.Currency.tiltFee (e:ℝ))
      (fun _ _=>IterationFour.Currency.tiltFee_nonneg _) enter
  change ‖(((f x/f β:ℝ):ℂ)^e)-(((f y/f β:ℝ):ℂ)^e)‖≤_
  rw [←Complex.ofReal_zpow,←Complex.ofReal_zpow,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
    div_zpow,div_zpow,←sub_div,abs_div,abs_of_pos hp]
  apply (div_le_iff₀ hp).mpr
  calc
    _ ≤ IterationFour.Currency.tiltFee (e:ℝ)*β⁻¹*f β^e*|x-y| := money
    _ ≤ rate k*β⁻¹*f β^e*|x-y| := by gcongr
    _ = _ := by ring

variable {G:Gauge} {n:Side} {V:Type} [DecidableEq V] {S:Census V}
    {D : V → ComparisonDensity.Address.Orbit}

def multiplier (a b:ℝ) (e:ℤ) (_:Fin (0+1)) : ℂ := (a:ℂ)^e-(b:ℂ)^e

def residual (P:MarkedPackets D G n S) (a b:ℝ) := copies P 0 (multiplier a b)

/-- The raw exponent, support and current marked roots are all identified by this one
bijection of addresses, before choosing any field or independent exterior test. -/
def address : ℕ≃ℕ := (index 0).trans (Equiv.prodUnique ℕ (Fin 1))

theorem term (P:MarkedPackets D G n S) (a b g:ℝ) (hg:g≠0) (i:ℕ) (x:TestSpace D) (U:Config G n) :
    (residual P a b).term x g U i=P.term x (a*g) U (address i)-P.term x (b*g) U (address i) := by
  rw [residual,copies_term P 0 (multiplier a b) g hg]
  have hj:(index 0 i).2.val=0:=by omega
  simp only [hj,mul_zero,pow_zero,mul_one,multiplier]
  change _=P.term x (a*g) U (index 0 i).1-P.term x (b*g) U (index 0 i).1
  cases h:P.packet (index 0 i).1 with
  | none => simp only [MarkedPackets.term,h,sub_self,mul_zero]
  | some t =>
    simp only [MarkedPackets.term,h,Complex.ofReal_mul,mul_zpow]
    ring

theorem paid (P:MarkedPackets D G n S) {β x y g:ℝ} (hβ:0<β)
    (hx:x∈IterationFour.Currency.stripe β) (hy:y∈IterationFour.Currency.stripe β) (hg:g≠0)
    {p:BudgetPoint} {sites:V→Support n}
    {region:Comparison.Density.Testing.Region (fun v=>(D v).Mood) n} {w:V→ℝ}
    {width bill:ℝ} {offset slope:ℕ}
    (H:P.Paid p sites region w g width bill offset slope) :
    let f:=IterationFour.Currency.gain
    (residual P (f x/f β) (f y/f β)).Paid p sites region w g width
      (bill*(rate P.powerCap*β⁻¹*|x-y|)) offset slope := by
  have hb:0≤rate P.powerCap*β⁻¹*|x-y|:=mul_nonneg
    (mul_nonneg (rate_nonnegative _) (inv_nonneg.mpr hβ.le)) (abs_nonneg _)
  apply copies_paid_of_bound P 0 _ g hg _ hb _ H
  intro e he
  simpa [multiplier] using scalar hβ hx hy P.powerCap e he

private theorem power_bound {u L:ℝ} (hu:0<u) (hL:1≤L) (up:u≤L) (down:1≤L*u)
    (k:ℕ) (e:ℤ) (he:|e|≤(k:ℤ)) : ‖(u:ℂ)^e‖≤L^k := by
  rw [norm_zpow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hu]
  cases e with
  | ofNat j =>
    have hj : j≤k := by
      change |(j:ℤ)|≤(k:ℤ) at he
      rw [abs_of_nonneg (Nat.cast_nonneg j)] at he
      exact_mod_cast he
    exact (pow_le_pow_left₀ hu.le up j).trans (pow_le_pow_right₀ hL hj)
  | negSucc j =>
    have hj : j+1≤k := by
      change |-((j+1:ℕ):ℤ)|≤(k:ℤ) at he
      rw [abs_neg,abs_of_nonneg (Nat.cast_nonneg _)] at he
      exact_mod_cast he
    have inv:u⁻¹≤L:=by rw [inv_eq_one_div]; exact (div_le_iff₀ hu).mpr down
    change (u^(j+1))⁻¹≤_
    rw [←inv_pow]
    exact (pow_le_pow_left₀ (inv_nonneg.mpr hu.le) inv _).trans (pow_le_pow_right₀ hL hj)

/-- The derivative may be measured on a different positive physical scalar from
the one at which the original finite packet bought its root bill. -/
theorem rebased (P:MarkedPackets D G n S) {β x y g L:ℝ} (hβ:0<β)
    (hx:x∈IterationFour.Currency.stripe β) (hy:y∈IterationFour.Currency.stripe β)
    (hg:0<g) (hL:1≤L) (up:IterationFour.Currency.gain β/g≤L)
    (down:1≤L*(IterationFour.Currency.gain β/g))
    {p:BudgetPoint} {sites:V→Support n}
    {region:Comparison.Density.Testing.Region (fun v=>(D v).Mood) n} {w:V→ℝ}
    {width bill:ℝ} {offset slope:ℕ}
    (H:P.Paid p sites region w g width bill offset slope) :
    let f:=IterationFour.Currency.gain
    (residual P (f x/g) (f y/g)).Paid p sites region w g width
      (bill*(L^P.powerCap*(rate P.powerCap*β⁻¹*|x-y|))) offset slope := by
  let f:=IterationFour.Currency.gain
  have fp:0<f β:=inv_pos.mpr (Real.sqrt_pos.mpr hβ)
  have hb:0≤L^P.powerCap*(rate P.powerCap*β⁻¹*|x-y|):=
    mul_nonneg (pow_nonneg (zero_le_one.trans hL) _) (mul_nonneg
      (mul_nonneg (rate_nonnegative _) (inv_nonneg.mpr hβ.le)) (abs_nonneg _))
  apply copies_paid_of_bound P 0 _ g hg.ne' _ hb _ H
  intro e he
  have fxy (t:ℝ): f t/g=f β/g*(f t/f β):=by
    field_simp [fp.ne',hg.ne']
  have main:‖((f x/g:ℝ):ℂ)^e-((f y/g:ℝ):ℂ)^e‖≤
      L^P.powerCap*(rate P.powerCap*β⁻¹*|x-y|):=by
    rw [fxy x,fxy y,Complex.ofReal_mul,Complex.ofReal_mul,mul_zpow,mul_zpow,←mul_sub,norm_mul]
    exact mul_le_mul (power_bound (div_pos fp hg) hL up down _ e he) (scalar hβ hx hy _ e he)
      (norm_nonneg _) (pow_nonneg (zero_le_one.trans hL) _)
  simpa [multiplier] using main

theorem read [Fintype V] (P:MarkedPackets D G n S) (a b g:ℝ) (hg:g≠0) (x:TestSpace D) (U:Config G n)
    (old:Summable (fun i=> Poly.send (P.mode i) (P.term x (b*g) U i)))
    (moved:Summable (fun i=> Poly.send (P.mode i) (P.term x (a*g) U i))) :
    (residual P a b).read x g U=P.read x (a*g) U-P.read x (b*g) U := by
  let f (i:ℕ):= Poly.send (P.mode i) (P.term x (a*g) U i)-Poly.send (P.mode i) (P.term x (b*g) U i)
  calc
    _ = ∑' i,f (address i) := by
      apply tsum_congr
      intro i
      rw [term P a b g hg]
      change Poly.send (P.mode (address i)) _=_
      apply YM.Marker.Poly.ext
      intro j
      by_cases hj:j=P.mode (address i) <;> simp [f,Poly.part_send,hj]
    _ = ∑' i,f i := address.tsum_eq _
    _ = _ := moved.tsum_sub old

end YM.Integration.QLocalMarkedCouplingDifference
