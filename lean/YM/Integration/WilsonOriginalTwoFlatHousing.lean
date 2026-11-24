import YM.Integration.WilsonOriginalTwoFlatOptical

/-! The optical estimate has a cutoff-uniform prefactor on its actual compact
housing. No span of the earlier separated experiment enters the price. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatHousing
open Function Finset Filter Lattice Wilson RG Tree Marker Multi QuadraticLocal Ac PhysicalNext.Repeat.Legato
open WilsonOriginalOccupiedCorridor
open scoped Classical BigOperators
open private allowance from YM.Integration.WilsonOriginalOccupiedRate

def charge (A:ℝ)(M n:ℕ):ℝ:=
  (2:ℝ)^n*(2*(((2^(2^n):ℕ):ℝ)*Real.exp ((A+2)*M))*n*Real.exp n)

private theorem compact {L:Side}(p:BudgetPoint)(Z:Support L)(n M:ℕ){A:ℝ}
    (h:p.supportExponent ≤ A)(z:coverNumber p.B Z ≤ M):WilsonOriginalFlatOccupiedRate.bill p Z 1 n ≤ charge A M n:=by
  have expBound:(p.supportExponent+2)*(coverNumber p.B Z:ℝ) ≤ (A+2)*M:=
    mul_le_mul (by linarith only [h]) (by exact_mod_cast z) (Nat.cast_nonneg _) (by linarith only [p.exponent_pos,h])
  dsimp only [WilsonOriginalFlatOccupiedRate.bill,WilsonOriginalFlatOccupiedRate.roof,charge]
  simp only [max_self,one_pow,mul_one]
  gcongr

variable {G:Gauge}(R:Run G)(simple:G.Simple){V:Type}[DecidableEq V]{J:Census V}
omit [DecidableEq V] in
private theorem shrunk (w:V→ℝ)(unit:∀v,w v≤1){b t:ℕ}(bt:b≤t):∀v,wallet R w bt v≤1:=by
  refine Nat.decreasingInduction (motive:=fun j jt=>∀v,wallet R w jt v≤1) ?_ ?_ bt
  · intro j h ih v
    rw [show wallet R w h.le=Stoop.radius (wallet R w h) (factor R j) from Nat.decreasingInduction_succ_left ..]
    exact (div_le_one (zero_lt_one.trans_le (le_max_left ..))).2 ((ih v).trans (le_max_left ..))
  · rw [show wallet R w (le_refl t)=w from Nat.decreasingInduction_self ..];exact unit

include simple in
theorem original (M:ℕ)(cap:ℝ):
    ∀ᶠ b:ℕ in atTop,∀(N per t:ℕ),b ≤ N → ∀(bt:b≤t)(s:J.Mode)(w:V→ℝ),
    (∀v,0<w v) → (∀v,w v≤1) → ∀(p:BudgetPoint)(Z:Support (R.family.side b per)),
    p.supportExponent ≤ cap → coverNumber p.B Z ≤ M →
    (shards J s).card+4*(Poly.toll (wallet R w bt) s+WilsonOriginalFlatOccupiedRate.bill p Z 1 s.val.card)*
      R.alloy.B.a.clock.hatBeta b*LocalComparison.forcedDivisor R.family b ≤
      ((shards J s).card:ℝ)+4*(1+charge cap M s.val.card):=by
  filter_upwards [allowance R simple 0 1 (show 0<(1:ℝ) by norm_num)] with b income N per t top bt s w wp w1 p Z capd small
  have phase:=income N per top
  simp only [pow_one,pow_zero,mul_one] at phase
  have wp':=positive R w wp bt
  have paid:Poly.toll (wallet R w bt) s ≤ 1:=
    prod_le_one (fun v _=>(wp' v).le) (fun v _=>shrunk R w w1 bt v)
  have bill:=compact p Z s.val.card M capd small
  let val:=Poly.toll (wallet R w bt) s+WilsonOriginalFlatOccupiedRate.bill p Z 1 s.val.card
  have val0:0≤val:=by
    have toll0:0≤Poly.toll (wallet R w bt) s:=(Poly.worth wp' s).le
    dsimp only [val,WilsonOriginalFlatOccupiedRate.bill,WilsonOriginalFlatOccupiedRate.roof];positivity
  have cash:4*val*R.alloy.B.a.clock.hatBeta b*LocalComparison.forcedDivisor R.family b ≤ 4*(1+charge cap M s.val.card):=
    calc 4*val*R.alloy.B.a.clock.hatBeta b*LocalComparison.forcedDivisor R.family b
      =4*val*(LocalComparison.forcedDivisor R.family b*R.family.path.levels.clock.hatBeta b):=by change 4*val*R.family.path.levels.clock.hatBeta b*_= _;ring
      _ ≤ 4*val*1:=mul_le_mul_of_nonneg_left phase (by positivity)
      _ ≤ _:=by rw [mul_one];exact mul_le_mul_of_nonneg_left (add_le_add paid bill) (by norm_num)

  exact add_le_add (le_refl ((shards J s).card:ℝ)) cash

end YM.Integration.WilsonOriginalTwoFlatHousing
end
