import YM.Integration.WilsonMovingLogForecast

/-! The actual published short-log `Day` has a before-regulator physical
rate for its original, growing table index. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMovingLogRate
open Filter Lattice Wilson RG PhysicalNext PhysicalNext.Repeat Legato Juniper
open scoped Classical Topology
variable {G:Gauge}

theorem physical (R:Run G) (simple:G.Simple) (r:ℕ) {a ε:ℝ}
    (order:8*a<7*(r+1:ℕ)) (positive:0≤a) (tender:0<ε) :
    ∀ᶠ m:ℕ in atTop, let j:=R.alloy.B.a.clock.J (m+1)
      r≤j ∧ ∀ N per, m<N → 7*(R.alloy.B.a.clock.hatBeta (m+1))^(Mulberry.aspiring j r) ≤
        ε*(Pert.Asymptotics.regulatorRun R.family N per (m+1))^a := by
  let X:=-(7:ℝ)/16*((r:ℝ)+1)
  have hx:X < -(a/2):=by dsimp [X];push_cast at order;linarith
  have deep := R.family.path.levels.fits.deep.comp (tendsto_add_atTop_nat 1)
  have warm:= (Next.Rank.Station.hat_rate R.family.path.levels simple).comp (tendsto_add_atTop_nat 1)
  filter_upwards [WilsonMovingLogCurrency.physical R simple positive hx tender,deep.eventually_ge_atTop r,
    warm.eventually_ge_atTop (1:ℝ)] with m hp rank hot
  refine ⟨rank,fun N per live=>le_trans ?_ (hp N per live)⟩
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.rpow_le_rpow_of_exponent_le (by exact hot)
  let j:=R.alloy.B.a.clock.J (m+1)
  have inv:(j+1:ℝ)⁻¹≤1:=inv_le_one_of_one_le₀ (by have hj : (0:ℝ)≤j:=Nat.cast_nonneg _;linarith)
  change Mulberry.aspiring j r≤X
  unfold Mulberry.aspiring Gauze.rampK LocalAtlas.leaf LocalAtlas.leew Sienna.vow X
  push_cast
  linarith

end YM.Integration.WilsonMovingLogRate
end
