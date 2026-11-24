import YM.Integration.WilsonOlderFreshSoftSocketFigureCurve
import YM.Integration.WilsonSeparatedPrefixKineticAdmitted

/-! The fixed planted-source exponent is paid at the measured older coupling. -/

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftSocketFigurePower
open Filter Real RG Primitives Wilson PhysicalNext.Repeat.Legato
open ActualRunPhysicalPages Pert.Asymptotics WilsonCoeffUV
open PhysicalNext PhysicalNext.Repeat
open WilsonSeparatedPrefixKineticGeometry

theorem absorbed {x θ E δ:ℝ}{p q:ℕ}(x0:0<x)(θ0:0<θ)(small:θ≤1)
    (ratio:3/4≤x/θ)(cost:0≤E+δ)(order:(q:ℝ)+E+δ≤p):
    exp (E*log x⁻¹)*(θ^p*x⁻¹^δ)≤(4/3:ℝ)^(E+δ)*θ^q:=by
  have inv:x⁻¹≤(4/3:ℝ)*θ⁻¹:=by
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ θ0).2
    rw [inv_mul_eq_div]
    apply (div_le_iff₀ x0).2
    have lower:=(le_div_iff₀ θ0).mp ratio
    linarith
  have price:=rpow_le_rpow (inv_nonneg.mpr x0.le) inv cost
  have spare:θ ^ (p:ℝ)*θ ^ (-(E+δ))≤θ^q:=by
    rw [←rpow_add θ0,←rpow_natCast θ q]
    apply rpow_le_rpow_of_exponent_ge θ0 small
    linarith
  calc
    _=θ^p*x⁻¹^(E+δ):=by
      rw [mul_comm E,exp_mul,exp_log (inv_pos.mpr x0),rpow_add (inv_pos.mpr x0)]
      ring
    _≤θ^p*((4/3:ℝ)*θ⁻¹)^(E+δ):=mul_le_mul_of_nonneg_left price (pow_nonneg θ0.le _)
    _=(4/3:ℝ)^(E+δ)*(θ^(p:ℝ)*θ^(-(E+δ))):=by
      rw [mul_rpow (by norm_num:0≤(4/3:ℝ)) (inv_nonneg.mpr θ0.le),inv_rpow θ0.le,rpow_neg θ0.le,rpow_natCast]
      ring
    _≤_:=mul_le_mul_of_nonneg_left spare (rpow_nonneg (by norm_num) _)

variable {G:Gauge}(R:Run G)
local notation "α" => R.family.S.a
local notation "H" => R.family.path.levels.clock.hatBeta
local notation "g" => regulatorRun R.family

theorem original (simple:G.Simple)(A:ℕ):∀ᶠv:ℕ in atTop,∀N per K,v≤K→K≤N→α v/α K≤(H v)^A→
    ∀(E δ:ℝ)(p q:ℕ),0≤E+δ→(q:ℝ)+E+δ≤p→
    exp (E*log (g N per K)⁻¹)*((g N per v)^p*(g N per K)⁻¹^δ)≤(4/3:ℝ)^(E+δ)*(g N per v)^q:=by
  obtain ⟨_,_,dated⟩:=WilsonSeparatedPrefixKineticGeometry.corridor R simple A
  filter_upwards [dated,WilsonSeparatedPrefixKineticGeometry.spend R simple 1 0] with v allowance close
  intro N per K vk live room E δ p q cost order
  have span:=WilsonSeparatedPrefixKineticAdmitted.admissible (R:=R) (simple:=simple) A v K vk room
  have ratio:=(allowance K N per vk live span).2 K vk le_rfl
  have θ0:=ActualRunKernelPackets.regulator_pos R N per v (vk.trans live)
  have inv:1≤(g N per v)⁻¹:=by simpa only [pow_zero,mul_one] using close N per (vk.trans live)
  exact absorbed (ActualRunKernelPackets.regulator_pos R N per K live) θ0 ((one_le_inv₀ θ0).mp inv)
    ratio.1 cost order

end YM.Integration.WilsonOlderFreshSoftSocketFigurePower
end
