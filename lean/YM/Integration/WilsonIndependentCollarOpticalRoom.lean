import YM.Integration.WilsonIndependentCollarOpticalCash
import YM.Integration.WilsonIndependentCollarClockRoom

/-! Fixed polynomial wages on the genuine moving physical clock have
arbitrarily small coupling degree, even on an optical collar. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonIndependentCollarOpticalRoom
open Filter RG Wilson PhysicalNext.Repeat.Legato WilsonCoeffUV.Bank WilsonCoeffUV.Mer WilsonCoeffUV.Cosmos
open scoped Topology

theorem original {G:Gauge} (R:Run G) (simple:G.Simple) (P:Credit) (B:ℝ) (k:ℕ)
    (_hB:1≤B) (ε:ℝ) (eps:0<ε):
    let H:=R.family.path.levels.clock.hatBeta
    ∀ᶠi:ℕ in atTop,∀β Z:ℝ,H (i+1)/2≤β → 1≤β → 1≤Z → 0≤Real.log (H (i+1)) →
      Z≤B*(1+Real.log (H (i+1)))^k → P.buy Z≤(Real.sqrt β)^ε:=by
  obtain ⟨n,hn⟩:=exists_nat_ge ε⁻¹
  have pos:0<n:=by exact_mod_cast lt_of_lt_of_le (inv_pos.mpr eps) hn
  have grown:1≤ε*n:=by
    have cmp:=mul_le_mul_of_nonneg_left hn eps.le
    rwa [mul_inv_cancel₀ eps.ne'] at cmp
  let a:=k*P.d
  let C:=P.buy B
  obtain paid:=WilsonIndependentCollarClockRoom.original R simple (C^n) (a*n)
  filter_upwards [paid] with i room
  intro β Z thermal hβ hZ late size
  let y:=1+Real.log (R.family.path.levels.clock.hatBeta (i+1))
  have low:0≤y:=by dsimp [y];linarith
  have roof:P.buy Z≤C*y^a:=by
    calc _ ≤ P.buy (B*y^k):=P.elder hZ size
         _ = C*y^a:=by unfold C Credit.buy a;rw [mul_pow,pow_mul];ring
  have charged:(P.buy Z)^n≤(C^n)*y^(a*n):=by
    rw [pow_mul,←mul_pow];exact pow_le_pow_left₀ (zero_le_one.trans (P.purchase hZ)) roof _
  have root:1≤Real.sqrt β:=by simpa using Real.sqrt_le_sqrt hβ
  apply (pow_le_pow_iff_left₀ (zero_le_one.trans (P.purchase hZ)) (Real.rpow_nonneg (Real.sqrt_nonneg _) _) pos.ne').mp
  apply (charged.trans (room β thermal)).trans
  rw [←Real.rpow_mul_natCast (Real.sqrt_nonneg _)]
  simpa only [Real.rpow_one,inv_inv] using Real.rpow_le_rpow_of_exponent_le root grown

end YM.Integration.WilsonIndependentCollarOpticalRoom
end
