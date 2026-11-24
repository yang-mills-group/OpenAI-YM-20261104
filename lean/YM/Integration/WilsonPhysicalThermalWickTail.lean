import YM.Integration.WilsonPhysicalThermalWickSurplus
import YM.Next.RANK.Planck

/-! On any original face the shield for the untrimmed group source
covers the full power restored on the external arms. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalThermalWickTail
open Filter Next.Rank Next.Rank.Perch Next.Rank.Glimmer Next.Rank.Common
open scoped Topology

theorem original (n k:ℕ)(A L:ℝ)(base:1≤A)(lord:0≤L):
    ∀ᶠ s:ℝ in atTop, ∀m:ℕ,m≤n→
      bill L s*(m*bill (-L-2) s*(A+bill (-L-2) s)^m * priced (bill (fuel k n) s) (n*k))≤
        bill (-3/2) s:=by
  filter_upwards [collected n k A base] with s purchased m hm
  have ξ:bill (-L-2) s≤bill (-2) s:=billed s (by linarith)
  have positive:0≤bill (-L-2) s:=(Real.exp_pos _).le
  have large:1≤A+bill (-L-2) s:=base.trans (le_add_of_nonneg_right positive)
  have mix:bill L s*bill (-L-2) s=bill (-2) s:=by rw [overlap];congr 1;ring
  let price:=priced (bill (fuel k n) s) (n*k)
  have pp:0≤price:=by unfold price priced;have := (Real.exp_pos (boil s*(fuel k n))).le;unfold bill;positivity
  calc
    _=m*bill (-2) s*(A+bill (-L-2) s)^m*price:=by rw [←mix];dsimp only [price];ring
    _≤n*bill (-2) s*(A+bill (-2) s)^n*price:=by
      apply mul_le_mul_of_nonneg_right _ pp
      apply mul_le_mul (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hm) (Real.exp_pos _).le) ?_ (by positivity) (by positivity)
      exact (pow_le_pow_right₀ large hm).trans (pow_le_pow_left₀ (zero_le_one.trans large) (by linarith) _)
    _≤_:=by
      apply le_trans _ purchased
      have p:0≤bill (-2) s:=(Real.exp_pos _).le
      have a:0≤A:=zero_le_one.trans base
      exact le_add_of_nonneg_right (mul_nonneg (pow_nonneg a _) (mul_nonneg p pp))

end YM.Integration.WilsonPhysicalThermalWickTail
end
