import YM.Integration.WilsonSeparatedPrefixKineticAppointed

/-! The literal inverse physical birth fee at K cancels the independently
computed power of the reversion series on the original v receiver. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonSeparatedPrefixKineticPole
open WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonReportingAbsoluteInletForecastBooks
open WilsonSeparatedPrefixKineticTruncation

def rent (h:ℕ):ℝ:=(2:ℝ)^h*h+2*h*3^h

theorem paid (q h:ℕ)(P:Cost){x y:ℝ}(x0:0<x)(x1:x ≤ 1)(y0:0<y)(xy:x/y ≤ 2)
    (roots:x*(mass (q+1) P)^h ≤ 1)(late:rent h*x ≤ 1)
    (numerical:|y-x*value (q+1) P x| ≤ x^(q+2)):
    |(x/y)^h*value (q+1) (P^h) x-1| ≤ x^q:=by
  let n:=q+1
  let z:=(x/y)*value n P x
  have ratio:|z-1| ≤ 2*x^n:=by
    calc
      _=|y-x*value n P x|/y:=by rw [abs_sub_comm z 1,←abs_of_pos y0,←abs_div];congr 1;dsimp [z];field_simp;rw [abs_of_pos y0]
      _ ≤ x^(n+1)/y:=div_le_div_of_nonneg_right numerical y0.le
      _= (x/y)*x^n:=by rw [pow_succ];ring
      _ ≤ _:=mul_le_mul_of_nonneg_right xy (pow_nonneg x0.le _)
  have bounded:|z-1| ≤ 2:=by simpa only [mul_one] using ratio.trans (mul_le_mul_of_nonneg_left (pow_le_one₀ x0.le x1) (by norm_num))
  have limit:|z| ≤ 3:=by have s:=abs_le.mp bounded;apply abs_le.mpr;constructor <;> linarith only [s.1,s.2]
  have anchor:|z^h-1| ≤ 2*x^n*h*3^h:=by
    have price:=abs_pow_sub_pow_le z 1 h
    rw [one_pow] at price
    have money:max |z| |(1:ℝ)| ≤ 3:=max_le limit (by norm_num)
    exact price.trans (mul_le_mul (mul_le_mul_of_nonneg_right ratio (Nat.cast_nonneg h))
      ((pow_le_pow_left₀ ((abs_nonneg _).trans (le_max_left ..)) money _).trans (pow_le_pow_right₀ (by norm_num:1 ≤ (3:ℝ)) (by omega))) (by positivity) (by positivity))
  have a:0 ≤ x/y:=div_nonneg x0.le y0.le
  have diff:|(x/y)^h*value n (P^h) x-z^h| ≤ (2:ℝ)^h*h*x^n:=by
    change |(x/y)^h*value n (P^h) x-((x/y)*value n P x)^h| ≤ _
    rw [mul_pow,←mul_sub,abs_mul,abs_of_nonneg (pow_nonneg a _)]
    calc
      _ ≤ (2:ℝ)^h*(h*x^(n+1)*(mass n P)^h):=mul_le_mul (pow_le_pow_left₀ a xy _) (powers n h P x0.le x1) (abs_nonneg _) (by positivity)
      _=((2:ℝ)^h*h*x^n)*(x*(mass n P)^h):=by rw [pow_succ];ring
      _ ≤ _:=mul_le_of_le_one_right (by positivity) roots
  calc
    _ ≤ (2:ℝ)^h*h*x^n+2*x^n*h*3^h:=(abs_sub_le _ (z^h) _).trans (add_le_add diff anchor)
    _=(rent h*x)*x^q:=by dsimp [n,rent];ring
    _ ≤ _:=mul_le_of_le_one_left (pow_nonneg x0.le _) late

open Function Filter Lattice Wilson RG RG.Supply Precision PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Pert.Asymptotics WilsonCoeffUV.Mer WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonOlderFreshSoftSocketKinetic
open WilsonSeparatedPrefixKineticMarket WilsonSeparatedPrefixKineticGeometry WilsonSeparatedPrefixKineticForecast
open scoped Topology Classical
variable {G:Gauge}(R:Run G)(simple:G.Simple)
local notation "V" => R.family.path.levels
local notation "g" => regulatorRun R.family

include simple in
theorem window (seller:ℕ→Gear G→ℝ)(sources:FundedMarkedCoverRows.prices seller R.kit)(q h A:ℕ):
    ∀ᶠ b:ℕ in atTop,∀K N per,b ≤ K→K ≤ N→span R A b K→
    let M:=kinetic V R.metals.O N K b
    |g N per K-g N per b*value (q+1) M (g N per b)| ≤ (g N per b)^(q+2)→
    |(g N per b/g N per K)^h*value (q+1) (M^h) (g N per b)-1| ≤ (g N per b)^q:=by
  obtain ⟨B,B1,geometry⟩:=corridor R simple A
  obtain ⟨C,gross⟩:=WilsonSeparatedPrefixKineticMarket.original R simple seller sources (q+1)
  let k:=((q+3:ℝ)*C.x*B^C.d)^h
  filter_upwards [geometry,gross,spend R simple k (C.d*h),spend R simple (max 1 (rent h)) 0] with b geo wealth stage endSale K N per bK KN admit M main
  let x:=g N per b
  let y:=g N per K
  have x0:0<x:=inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson (bK.trans KN)))
  have y0:0<y:=inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson KN))
  obtain ⟨⟨z1,a1,ap,_⟩,clocks⟩:=geo K N per bK KN admit
  let z:=wage R b
  have wage':(mass (q+1) M)^h ≤ k*z^(C.d*h):=by
    have aa:mass (q+1) M ≤ ((q:ℝ)+3)*C.buy (B*z):=by
      have funds:=(wealth N K bK KN).1 b le_rfl bK
      push_cast at funds
      rw [show (q:ℝ)+1+2=q+3 by ring] at funds
      exact funds.trans (mul_le_mul_of_nonneg_left (C.elder a1 ap) (by positivity))
    refine (pow_le_pow_left₀ (mass_nonneg ..) aa h).trans_eq ?_
    have equal:((q:ℝ)+3)*C.buy (B*z)=(((q:ℝ)+3)*C.x*B^C.d)*z^C.d:=by unfold Credit.buy;rw [mul_pow];ring
    rw [equal,mul_pow,pow_mul]
  have lux:max 1 (rent h) ≤ x⁻¹:=by simpa only [pow_zero,mul_one] using endSale N per (bK.trans KN)
  have commute (t:ℝ)(cost:t ≤ x⁻¹):t*x ≤ 1:=(mul_le_mul_of_nonneg_right cost x0.le).trans_eq (inv_mul_cancel₀ x0.ne')
  have one:= commute 1 ((le_max_left ..).trans lux)
  have stage':(mass (q+1) M)^h ≤ x⁻¹:=wage'.trans (stage N per (bK.trans KN))
  have lb:3/4*x ≤ y:=(le_div_iff₀ x0).mp ((clocks K bK le_rfl).1)
  exact paid q h M x0 (by simpa only [one_mul] using one) y0 ((div_le_iff₀ y0).mpr (by linarith only [lb,x0.le]))
    (by change x*(mass (q+1) M)^h≤1;rw [mul_comm];exact commute _ stage') (commute _ ((le_max_right ..).trans lux)) main

end YM.Integration.WilsonSeparatedPrefixKineticPole
end
