import YM.Integration.WilsonVacuumPreResetSameIncome
import YM.Integration.WilsonVacuumPreResetRenderTime

/-! Cost of the actual upstream temperature at the same calendar record. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetSameTime
open Filter Lattice RG Wilson WilsonStartup Pert.Asymptotics PhysicalNext.Repeat.Legato
open AnalyticBridge VerifiedReset RG01Estimate WilsonCoeffUV WilsonCoeffUV.Bank
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Physical WilsonLimitConstruction
open scoped Topology
variable {G:Gauge}

theorem ratios (R:Run G)(simple:G.Simple):
    ∀ᶠ m:ℕ in atTop,∀N per:ℕ,m<N → regulatorRun R.family N per m≤3*regulatorRun R.family N per (m+1):=by
  let V:=R.family.path.levels
  filter_upwards [RG01.Physical.nextHat simple V] with m next
  intro N per later
  let b:=R.family.path.β N per m
  let c:=R.family.path.β N per (m+1)
  have before:V.clock.hatBeta m/2≤b:=(R.makes.wilson.represents N per m later.le).band.1
  have after:c≤2*V.clock.hatBeta (m+1):=(R.makes.wilson.represents N per (m+1) later).band.2
  have bp:0<b:=(half_pos (zero_lt_one.trans (V.fits.delayed m))).trans_le before
  have cp:0<c:=(half_pos (zero_lt_one.trans (V.fits.delayed (m+1)))).trans_le (R.makes.wilson.represents N per (m+1) later).band.1
  have sq:Real.sqrt c≤3*Real.sqrt b:=(Real.sqrt_le_left (by positivity)).2
    (by nlinarith only [before,after,next,bp.le,Real.sq_sqrt bp.le])
  change (Real.sqrt b)⁻¹≤3*(Real.sqrt c)⁻¹
  rw [←one_div,←div_eq_mul_inv]
  exact (div_le_div_iff₀ (Real.sqrt_pos.mpr bp) (Real.sqrt_pos.mpr cp)).2 (by simpa using sq)

theorem original (R:Run G)(simple:G.Simple)(bar:RG01Estimate.Chart.Barrier R.alloy
    (fun _ i=>((i:ℝ)+1)⁻¹))(K:ℝ)(kp:0≤K){ε:ℝ}(ep:0<ε):
    let V:=R.family.path.levels
    ∀ᶠ m:ℕ in atTop,∀N per:ℕ,m<N→K*(regulatorRun R.family N per m)^(11/4:ℝ)≤ε*Time.forecastE V m:=by
  intro V
  let s:ℝ:=11/4
  have hp:0≤K*(3:ℝ)^s:=mul_nonneg kp (by positivity)
  filter_upwards [ratios R simple,WilsonVacuumPreResetRenderTime.original R simple bar _ hp ep] with m both heat
  intro N per later
  let g:=regulatorRun R.family N per m
  let g':=regulatorRun R.family N per (m+1)
  have gp:0<g:=IterationFour.Currency.g_pos R.makes N per m later.le
  have fp:0<g':=IterationFour.Currency.g_pos R.makes N per (m+1) later
  calc
    K*g^s≤K*(3*g')^s:=mul_le_mul_of_nonneg_left (Real.rpow_le_rpow gp.le (both N per later) (by norm_num [s])) kp
    _=K*(3:ℝ)^s*g'^s:=by rw [Real.mul_rpow (by norm_num) fp.le];ring
    _≤_:=heat N per later

end YM.Integration.WilsonVacuumPreResetSameTime
