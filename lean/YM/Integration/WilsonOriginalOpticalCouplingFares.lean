import YM.Integration.WilsonOriginalOpticalCouplingBand

/-! A dated monomial of the true clock and the true measured coupling has a fixed reporting pole. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalOpticalCouplingFares
open Filter Lattice Wilson RG
open PhysicalNext PhysicalNext.Repeat Legato Org AllOrder AllOrder.Floe AllOrder.Floe.Step
open AllOrder.Floe.Step.PlanV AllOrder.Transit WheelP AnalyticBridge VerifiedReset Pressure Pert.Asymptotics
open scoped Topology
variable {G:Gauge}(R:Run G)(simple:G.Simple)
local notation "H" i:max => R.family.path.levels.clock.hatBeta i
local notation "g" N:max per:max i:max => regulatorRun R.family N per i

include simple in
theorem fee (t e f:ℕ)(C:ℝ)(hp:0 ≤ C):∀ᶠ b:ℕ in atTop,∀{N per K i j:ℕ},
    b ≤ i → i ≤ K → b ≤ j → j ≤ K → K ≤ N → R.family.S.a b/R.family.S.a K ≤ (H b)^t →
    C*(H i)^e*((g N per j)⁻¹)^f ≤ ((g N per b)⁻¹)^(2*e+f+1):=by
  filter_upwards [WilsonOriginalOpticalCouplingBand.scale R simple t,WilsonOriginalOpticalCouplingBand.cold R simple (C*4^e*3^f)] with b band opening
  intro N per K i j bi ik bj jk live re
  have Hpos:0 ≤ H i:=(zero_lt_one.trans (R.family.path.levels.fits.delayed i)).le
  let z:=(g N per b)⁻¹
  have z0:0 ≤ z:=by change 0 ≤ ((Real.sqrt _)⁻¹)⁻¹;positivity
  have gj:0 ≤ (g N per j)⁻¹:=by change 0 ≤ ((Real.sqrt _)⁻¹)⁻¹;positivity
  have h:(H i) ≤ 4*z^2:=(band (per:=per) bi ik live re).2.1
  have jh:(g N per j)⁻¹ ≤ 3*z:=(band bj jk live re).2.2.2.2
  have co:C*4^e*3^f ≤ z:=opening N per (bi.trans (ik.trans live))
  calc C*(H i)^e*((g N per j)⁻¹)^f ≤ C*(4*z^2)^e*(3*z)^f:=by
         exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ Hpos h _) hp)
           (pow_le_pow_left₀ gj jh _) (pow_nonneg gj _) (mul_nonneg hp (by positivity))
       _ = (C*4^e*3^f)*z^(2*e+f):=by rw [pow_add,pow_mul,mul_pow,mul_pow];ring
       _ ≤ z*z^(2*e+f):=mul_le_mul_of_nonneg_right co (pow_nonneg z0 _)
       _ = z^(2*e+f+1):=by rw [pow_succ,mul_comm]

include simple in
theorem gain (t p:ℕ)(C:ℝ)(hp:0 ≤ C):∀ᶠ b:ℕ in atTop,∀{N per K i:ℕ},
    b ≤ i → i ≤ K → K ≤ N → R.family.S.a b/R.family.S.a K ≤ (H b)^t →
    C*(g N per i)^(p+1) ≤ (g N per b)^p:=by
  filter_upwards [WilsonOriginalOpticalCouplingBand.scale R simple t,WilsonOriginalOpticalCouplingBand.cold R simple (C*2^(p+1))] with b band opening
  intro N per K i bi ik live re
  let z:=g N per b
  have mini:(H b)/2 ≤ R.family.path.β N per b:=(R.makes.wilson.represents N per b (bi.trans (ik.trans live))).band.1
  have paid:0 < H b:=zero_lt_one.trans (R.family.path.levels.fits.delayed b)
  have z0:0<z:=inv_pos.mpr (Real.sqrt_pos.mpr (by linarith only [paid,mini]))
  have gi:0 ≤ g N per i:=by change 0 ≤ (Real.sqrt _)⁻¹;positivity
  have h:(g N per i) ≤ 2*z:=(band bi ik live re).2.2.1
  have co:C*2^(p+1) ≤ z⁻¹:=opening N per (bi.trans (ik.trans live))
  calc C*(g N per i)^(p+1) ≤ C*(2*z)^(p+1):=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ gi h _) hp
       _ = (C*2^(p+1))*z^(p+1):=by rw [mul_pow];ring
       _ ≤ z⁻¹*z^(p+1):=mul_le_mul_of_nonneg_right co (pow_nonneg z0.le _)
       _ = z^p:=by rw [pow_succ];field_simp

end YM.Integration.WilsonOriginalOpticalCouplingFares
end
