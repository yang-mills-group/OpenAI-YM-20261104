import YM.Integration.WilsonOriginalTwoFlatHousing

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativeTrialCoveredRate
open Function Finset Filter Lattice Wilson RG Tree Marker Multi QuadraticLocal Ac PhysicalNext.Repeat.Legato
open WilsonOriginalOccupiedCorridor WilsonOriginalTwoFlatHousing
open scoped Classical BigOperators
open private allowance from YM.Integration.WilsonOriginalOccupiedRate
open private compact shrunk from YM.Integration.WilsonOriginalTwoFlatHousing
variable {G:Gauge}(R:Run G)(simple:G.Simple){V:Type}[DecidableEq V]{J:Census V}

include simple in
/-- A fixed finite housing consumes one unit of the original compulsory
allowance at its receiving date, uniformly over the later fine cutoff. -/
theorem original (cap:ℝ)(M n:ℕ):
    ∀ᶠ b:ℕ in atTop,∀(N per t:ℕ),b ≤ N → ∀(bt:b ≤ t)(s:J.Mode),s.val.card ≤ n →
    ∀(w:V→ℝ), (∀v,0 < w v) → (∀v,w v ≤ 1) → ∀(p:BudgetPoint)(Z:Support (R.family.side b per)),
    p.supportExponent ≤ cap → coverNumber p.B Z ≤ M →
    4*(Poly.toll (wallet R w bt) s+WilsonOriginalFlatOccupiedRate.bill p Z 1 s.val.card)*
      R.alloy.B.a.clock.hatBeta b*LocalComparison.forcedDivisor R.family b ≤ 1:=by
  let fee:=fun k=>|4*(1+charge cap M k)|
  let bound:ℝ:=1+∑k∈range (n+1),fee k
  have pos:0<bound:=lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_right (sum_nonneg (fun _ _=>abs_nonneg _)))
  filter_upwards [allowance R simple 0 1 (inv_pos.mpr pos)] with b income N per t top bt s many w wp small p Z capd room
  have phase:=income N per top
  simp only [pow_one,pow_zero,mul_one] at phase
  have paid:Poly.toll (wallet R w bt) s ≤ 1:=
    prod_le_one (fun v _=>(positive R w wp bt v).le) (fun v _=>shrunk R w small bt v)
  have compactFee:=compact p Z s.val.card M capd room
  have sumFee:fee s.val.card ≤ ∑k∈range (n+1),fee k:=
    single_le_sum (fun k _=>abs_nonneg (4*(1+charge cap M k))) (mem_range.mpr (Nat.lt_succ_of_le many))
  have cost:4*(Poly.toll (wallet R w bt) s+WilsonOriginalFlatOccupiedRate.bill p Z 1 s.val.card) ≤ bound:=by
    calc _ ≤ 4*(1+charge cap M s.val.card):=mul_le_mul_of_nonneg_left (add_le_add paid compactFee) (by norm_num)
         _ ≤ fee s.val.card:=le_abs_self _
         _ ≤ _:=sumFee.trans (le_add_of_nonneg_left zero_le_one)
  have hp:0≤R.alloy.B.a.clock.hatBeta b:=(zero_lt_one.trans (R.family.path.levels.fits.delayed b)).le
  have kp:0 < LocalComparison.forcedDivisor R.family b:=Real.sqrt_pos.2 (Real.exp_pos _)
  calc _ = 4*(Poly.toll (wallet R w bt) s+WilsonOriginalFlatOccupiedRate.bill p Z 1 s.val.card)*
          (LocalComparison.forcedDivisor R.family b*R.alloy.B.a.clock.hatBeta b):=by ring
       _ ≤ bound*(LocalComparison.forcedDivisor R.family b*R.alloy.B.a.clock.hatBeta b):=
         mul_le_mul_of_nonneg_right cost (mul_nonneg kp.le hp)
       _ ≤ bound*bound⁻¹:=mul_le_mul_of_nonneg_left phase pos.le
       _ = 1:=mul_inv_cancel₀ pos.ne'
end YM.Integration.WilsonOriginalAlternativeTrialCoveredRate
end
