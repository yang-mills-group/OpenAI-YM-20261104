import YM.Integration.WilsonLimitConstruction.FundedWilsonBackgroundEnvelope
import YM.Integration.WilsonLimitConstruction.FundedPruningRate
import YM.Extra.WILSON_STARTUP.Fast
import YM.MatchingLedger.Compass.Deck

/-! The sparse finite-cutoff price is paid, with arbitrary leading constant,
at each requested coarse station. One original calendar threshold works before
all later cutoffs, periods, normalized fields and stopping configurations. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedWilsonSparsePrice

open Function Filter Set Lattice RG Exterior
open PhysicalNext.Repeat.Legato Pert.Asymptotics MatchingLedger.Compass.Income
open FundedWilsonBackgroundEnvelope FundedWilsonSparseSupport
open scoped Topology
variable {G : Gauge}

theorem compare (R : Run G) (hG : G.Simple) (N p i : ℕ) (hi : i ≤ N) :
    regulatorRun R.family N p N ≤ 4 * regulatorRun R.family N p i := by
  let D := R.family.path.levels
  have hmono := WilsonStartup.Timing.hat_mono D (Gauge.slopeConstant_pos hG).le hi
  have hpos : 0 < Real.sqrt (D.clock.hatBeta i) := Real.sqrt_pos.mpr (WardBin.hot D i)
  have hm : D.clock.hatCoupling N ≤ D.clock.hatCoupling i :=
    inv_anti₀ hpos (Real.sqrt_le_sqrt hmono)
  have hf := (Weather.into_band R.family R.makes (m:=N) (N:=N) le_rfl p).2
  have hc := (Weather.into_band R.family R.makes hi p).1
  linarith only [hm,hf,hc]

theorem small (R : Run G) (hG : G.Simple) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ i : ℕ in atTop, ∀ N p, i ≤ N → regulatorRun R.family N p i < δ := by
  let D := R.family.path.levels
  filter_upwards [(WardBin.bell D hG).eventually_ge_atTop ((4/δ)^2)] with i hi N p hN
  have hb := WardBin.hot D i
  have hs := (Real.le_sqrt (div_nonneg (by norm_num : 0≤(4:ℝ)) hδ.le) hb.le).2 hi
  have hp := Real.sqrt_pos.mpr hb
  have h := (Weather.into_band R.family R.makes hN p).2
  change _ ≤ 2*(Real.sqrt (D.clock.hatBeta i))⁻¹ at h
  rw [←div_eq_mul_inv] at h
  exact h.trans_lt ((div_lt_iff₀ hp).2 (by nlinarith only [(div_le_iff₀ hδ).1 hs]))

theorem prices (R : Run G) (hG : G.Simple) (r s : ℕ) {C ε η : ℝ}
    (hC : 0 < C) (hε : 0 < ε) (hη : 0 < η) :
    ∀ᶠ i : ℕ in atTop, ∀ N p, i ≤ N → ∀ B : fieldDir G (R.family.side N p) 1,
      (links B).card ≤ s →
      let t := regulatorRun R.family N p N
      let g := regulatorRun R.family N p i
      let q := cost C r B t
      0 < t ∧ ‖t‖ ≤ 1 ∧ q ≤ ε*g^((r:ℝ)+1-η) ∧ Real.exp q - 1 ≤ ε*g^((r:ℝ)+1-η) := by
  let M := ((6*s : ℕ):ℝ) * C * (4:ℝ)^(r+1)
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have ht₁ : Tendsto (fun x : ℝ => M*x^(r+1)) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun x : ℝ => M*x^(r+1)) := continuous_const.mul (continuous_id.pow (r+1))
    have h : Tendsto (fun x : ℝ => M*x^(r+1)) (𝓝 0) (𝓝 (M*(0:ℝ)^(r+1))) := hc.tendsto 0
    simpa only [zero_pow (Nat.succ_ne_zero _),mul_zero] using h
  have ht₂ : Tendsto (fun x : ℝ => (2*M)*x^η) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun x : ℝ => (2*M)*x^η) := continuous_const.mul (Real.continuous_rpow_const hη.le)
    have h : Tendsto (fun x : ℝ => (2*M)*x^η) (𝓝 0) (𝓝 ((2*M)*(0:ℝ)^η)) := hc.tendsto 0
    simpa only [Real.zero_rpow hη.ne',mul_zero] using h
  have hsmall : ∀ᶠ x : ℝ in 𝓝 0, x < 1/4 ∧ M*x^(r+1)<1 ∧ (2*M)*x^η < ε := by
    filter_upwards [gt_mem_nhds (by norm_num : (0:ℝ)<1/4),
        ht₁.eventually (gt_mem_nhds zero_lt_one),ht₂.eventually (gt_mem_nhds hε)] with x hx hx₁ hx₂
    exact ⟨hx,hx₁,hx₂⟩
  obtain ⟨δ,hδ,hd⟩ := Metric.mem_nhds_iff.mp hsmall
  filter_upwards [small R hG hδ] with i hi N p hiN B hs
  let t := regulatorRun R.family N p N
  let g := regulatorRun R.family N p i
  let q := cost C r B t
  have htp : 0 < t := Weather.runs_pos R.family R.makes le_rfl p
  have hgp : 0 < g := Weather.runs_pos R.family R.makes hiN p
  have hg := hd (show g ∈ Metric.ball 0 δ by simpa only [Metric.mem_ball,dist_zero_right,Real.norm_of_nonneg hgp.le] using hi N p hiN)
  have htg : t ≤ 4*g := compare R hG N p i hiN
  have hq : 0 ≤ q := by dsimp only [q,cost]; positivity
  have hqm : q ≤ M*g^(r+1) := by
    calc
      q ≤ ((6*s:ℕ):ℝ) * (C * (4*g)^(r+1)) := by
        unfold q cost
        rw [Real.norm_of_nonneg htp.le]
        exact mul_le_mul (by exact_mod_cast Nat.mul_le_mul_left 6 hs)
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ htp.le htg _) hC.le)
          (mul_nonneg hC.le (pow_nonneg htp.le _)) (Nat.cast_nonneg _)
      _ = _ := by rw [mul_pow]; dsimp only [M]; ring
  have hfac : g^(r+1) = g^η * g^((r:ℝ)+1-η) := by
    rw [←Real.rpow_add hgp,←Real.rpow_natCast]
    congr 1
    push_cast
    ring
  have hr : 2*q ≤ ε*g^((r:ℝ)+1-η) := calc
    _ ≤ 2*(M*g^(r+1)) := by linarith only [hqm]
    _ = (2*M*g^η)*g^((r:ℝ)+1-η) := by rw [hfac]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hg.2.2.le (Real.rpow_nonneg hgp.le _)
  have he := Real.abs_exp_sub_one_le (x:=q) (by rw [abs_of_nonneg hq]; exact hqm.trans hg.2.1.le)
  rw [abs_of_nonneg hq] at he
  exact ⟨htp,by rw [Real.norm_of_nonneg htp.le]; linarith only [htg,hg.1],
    (by linarith only [hq,hr]),(le_abs_self _).trans (he.trans hr)⟩

end YM.Integration.WilsonLimitConstruction.FundedWilsonSparsePrice
end
