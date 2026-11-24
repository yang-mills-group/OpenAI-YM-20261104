import YM.Integration.WilsonOriginalAlternativeTrialSeparationRate

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativeTrialThermalRate
open Filter Lattice Wilson RG PhysicalNext PhysicalNext.Repeat Legato
open WilsonThermometerMixedCollarSubpower Pert.Asymptotics
open scoped Topology
variable {G:Gauge}(R:Run G)
local notation "H" j:max => R.family.path.levels.clock.hatBeta j

theorem original (simple:G.Simple)(n a p:ℕ)(C e:ℝ)(c0:0≤C)(ep:0<e):
    ∀ᶠ f:ℕ in atTop,∀N per,f≤N→∀l B:ℕ,(l:ℝ)≤C*(1+Real.log (H f))→(Real.log (H f))^2≤(B:ℝ)→
      H f^a*Real.exp ((n:ℝ)*(l:ℝ)*(scale (H f))^3)*Real.exp (-(2:ℝ)*((B/8:ℕ):ℝ))≤e*(regulatorRun R.family N per f)^p:=by
  have hot:=Next.Rank.Station.hat_rate R.family.path.levels simple
  filter_upwards [hot.eventually_ge_atTop (2:ℝ),hot.eventually (WilsonOriginalAlternativeTrialSeparationRate.original n a p C e c0 ep)] with f h2 fare N per live l B span area
  let β:=R.family.path.β N per f
  have realβ:β≤2*H f:=(R.makes.wilson.represents N per f live).band.2
  have hp:0<H f:=by linarith only [h2]
  have sq:β≤(H f)^2:=by nlinarith only [realβ,mul_nonneg hp.le (sub_nonneg.2 h2)]
  have gp:=ActualRunKernelPackets.regulator_pos R N per f live
  change 0<(Real.sqrt β)⁻¹ at gp
  have g:(H f)⁻¹≤regulatorRun R.family N per f:=by
    apply (inv_le_inv₀ hp (inv_pos.mp gp)).2
    exact (Real.sqrt_le_iff.mpr ⟨hp.le,sq⟩)
  exact (fare l B span area).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (inv_nonneg.2 hp.le) g p) ep.le)

end YM.Integration.WilsonOriginalAlternativeTrialThermalRate
end
