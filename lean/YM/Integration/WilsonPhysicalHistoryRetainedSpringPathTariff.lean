import YM.Integration.WilsonPhysicalHistoryRetainedSpringMomentPrice
import YM.Integration.WilsonPhysicalHistoryRetainedSpringPitchSubpower
import YM.Integration.WilsonPhysicalHistoryRetainedSpringGrowth

/-! The old cubic and quartic have the radius of the actual previous path.
Their price uses that radius and the signed measured pitch at date m+1. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open Filter Lattice RG Wilson Pressure WilsonStartup Pert.Asymptotics
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato ConnectedActivityE6
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Physical RGLocalTaylor
open scoped Topology BigOperators Classical
variable {G : Gauge}

private theorem old_path_cost (R : Run G) (simple : G.Simple) (slow : WilsonWindowReportingPace.Slow R.kit)
    (k : ℕ) {η : ℝ} (hp : 0<η) :
    let V:=R.family.path.levels
    ∀ᶠ m : ℕ in atTop,∀ N per : ℕ,m<N →
      let D:=V.params (m+1)
      D.paths*D.width⁻¹^k≤(regulatorRun R.family N per (m+1))^(-η) := by
  intro V
  let C : Credit:=⟨1,k+1,by linarith [Nat.cast_nonneg (α:=ℝ) k]⟩
  filter_upwards [(tendsto_add_atTop_nat 1).eventually (exp_at_band C V simple η hp)]
    with m age
  intro N per later D
  let j:=m+1
  let z:=zz V j
  have logpos : 0<Real.log (V.clock.hatBeta j):=Real.log_pos (V.fits.delayed j)
  have logcap : Real.log (V.clock.hatBeta j)≤Real.exp z:=by
    rw [←Real.exp_log logpos]
    apply Real.exp_le_exp.mpr
    change Real.log (Real.log (V.clock.hatBeta j))≤1+Real.log (Real.log (V.clock.hatBeta j))
    linarith
  have stage : ActualRunAdmissionScales.profileCost V j≤Real.exp z:=calc
    _ ≤ ((V.S.block m).val:ℝ) := ActualRunAdmissionScales.profileCost_le_block V m
    _ ≤ Real.log (V.clock.hatBeta m) := WilsonFundedMeasuredWindow.paced R slow m
    _ ≤ Real.log (V.clock.hatBeta j):=Real.log_le_log (zero_lt_one.trans (V.fits.delayed m)) (Push.Corrected.Last.band_le V simple (Nat.le_succ m))
    _ ≤ _ := logcap
  have components:=ActualRunAdmissionScales.profileCost_components V j
  have width : D.width⁻¹≤Real.exp z:=components.1.trans stage
  have path : D.paths≤Real.exp z:=components.2.1.trans stage
  apply le_trans _ (age (R.family.path.β N per j) (R.makes.wilson.represents N per j later).band.1)
  calc _ ≤ Real.exp z * (Real.exp z)^k:=by
          exact mul_le_mul path (pow_le_pow_left₀ (inv_nonneg.mpr D.width_pos.le) width _) (pow_nonneg (inv_nonneg.mpr D.width_pos.le) _) (Real.exp_pos _).le
    _ = Real.exp (C.buy z):=by
          rw [←Real.exp_nat_mul,←Real.exp_add]
          congr 1
          change _=(k+1:ℝ)*z^1
          ring

theorem cofinal_path_tariff (R : Run G) (simple : G.Simple) (slow : WilsonWindowReportingPace.Slow R.kit)
    (v : ℕ→Gear G→ℝ) (rows : FundedMarkedCoverRows.prices v R.kit) (r u k : ℕ)
    {ε η : ℝ} (ep : 0<ε) (hp : 0<η) :
    let V:=R.family.path.levels
    ∀ᶠ m : ℕ in atTop,∀ N per : ℕ,m+1<N →
      let j:=m+1
      let L:=(V.clock.op m per).patch.L
      let g:=regulatorRun R.family N per j
      let w:=g^2*pitchTail R N j r g+R.alloy.B.kin.alpha N j
      let D:=V.params j
      ∀ {W : ℝ} (o : Target.Order G W),
      WilsonCoherentMayerCovarianceCalendar.deviation G L o≤1+Real.log (betaF G (V.clock.hatBeta m) L) →
      |w| *(D.paths*(2*speedPrice G L o.eta o.gap o.ample u/D.width)^k)≤ε*g^(-η) := by
  intro V
  let t:=η/3
  let c:=(r-2+1:ℕ)+1
  have t0 : 0<t:=by dsimp only [t]; positivity
  have c0 : (0:ℝ)<c:=by dsimp only [c]; positivity
  filter_upwards [old_path_cost R simple slow k t0,cofinal_speed R simple u k 0 (div_pos ep c0) t0,
    (tendsto_add_atTop_nat 1).eventually (pitch_subpower R simple v rows r t0),
    (tendsto_add_atTop_nat 1).eventually ((stamp_lim V simple).eventually_ge_atTop 1),
    (tendsto_add_atTop_nat 1).eventually (IterationFour.Currency.g_small simple R.makes 1 zero_lt_one)]
    with m path speed tuned stage chilled
  intro N per later j L g w D W o paid
  have gp : 0<g:=IterationFour.Currency.g_pos R.makes N per j later.le
  have limit : g≤1:=(chilled N per later.le).le
  have one : g^2≤1:=pow_le_one₀ gp.le limit
  have pitch:=tuned N later per
  have weight : |w|≤(c:ℝ)*g^(-t):=by
    calc _ ≤ |g^2*pitchTail R N j r g|+|R.alloy.B.kin.alpha N j|:=abs_add_le .. 
      _ ≤ (((r-2+1:ℕ):ℝ)*g^(-t))+g^(-t):=by
        rw [abs_mul,abs_of_nonneg (pow_nonneg gp.le _)]
        exact add_le_add ((mul_le_of_le_one_left (abs_nonneg _) one).trans pitch.2.2) pitch.1
      _ = _:=by simp only [c,Nat.cast_add,Nat.cast_one]; ring
  have M:=(speed_price_pos G L o.eta o.gap o.ample u).le
  let A:=2*speedPrice G L o.eta o.gap o.ample u
  have m0 : 0≤A:=by dsimp only [A]; positivity
  have entered:=speed N per (Nat.lt_of_succ_lt later) (σ:=1) zero_lt_one (by simpa using stage) o paid
  have checked : A^k≤ε/c*g^(-t):=by
    apply le_trans _ entered
    simp only [A,Nat.zero_add,pow_one,div_one]
    linarith [pow_nonneg m0 k]
  have rooted : D.paths*D.width⁻¹^k≤g^(-t):=path N per (Nat.lt_of_succ_lt later)
  have gross : g^(-t)*g^(-t)*g^(-t)=g^(-η):=by
    rw [←Real.rpow_add gp,←Real.rpow_add gp]
    congr 1
    dsimp only [t]
    ring
  calc
    _ = (|w| *(D.paths*D.width⁻¹^k))*A^k := by
      dsimp only [A]
      rw [div_eq_mul_inv,mul_pow]
      ring
    _ ≤ ((c:ℝ)*g^(-t)*g^(-t))*(ε/c*g^(-t)) := by
      apply mul_le_mul _ checked (pow_nonneg m0 _) (by positivity)
      exact mul_le_mul weight rooted (mul_nonneg D.paths_pos.le (pow_nonneg (inv_nonneg.mpr D.width_pos.le) _)) (by positivity)
    _ = _:=by rw [←gross]; field_simp

end YM.Integration.OriginalMarkedRunAction
