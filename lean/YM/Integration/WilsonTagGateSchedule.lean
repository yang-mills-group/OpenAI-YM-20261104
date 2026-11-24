import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Draught

/-! Numerical gates for rooted physical likelihoods, purchased after the blocking shape
and before the fine temperature. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonTagGateSchedule
open Filter Pressure RG
open scoped Topology

theorem cooling : Tendsto (fun z : ℝ => (Real.sqrt z)⁻¹ * (Real.log z)^12) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop ((12:ℕ):ℝ)
    (show 0 < (1/2:ℝ) by norm_num)).tendsto_div_nhds_zero
  have hl : Tendsto (fun z : ℝ => (Real.log z)^12 / z^(1/2:ℝ)) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast] using h
  have eq (z : ℝ) : (Real.sqrt z)⁻¹*(Real.log z)^12 = (Real.log z)^12/z^(1/2:ℝ) := by
    rw [Real.sqrt_eq_rpow,div_eq_mul_inv ((Real.log z)^12) (z^(1/2:ℝ)),mul_comm]
  exact hl.congr' (Eventually.of_forall fun z => (eq z).symm)

theorem rare (C : ℝ) (q : ℕ) : ∀ᶠ z : ℝ in atTop,
    C*Real.exp (-(Real.log z)^2) ≤ (z^q)⁻¹ := by
  filter_upwards [eventually_ge_atTop C,eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop ((q+1:ℕ):ℝ)] with z hz hpos hlog
  have h0 : 0 < z := zero_lt_one.trans hpos
  have hl : 0 ≤ Real.log z := (Real.log_pos hpos).le
  rw [← one_div,le_div_iff₀ (pow_pos h0 q)]
  calc
    _ ≤ z*Real.exp (-(Real.log z)^2)*z^q := by
      gcongr
    _ = z^(q+1)*Real.exp (-(Real.log z)^2) := by ring
    _ = Real.exp (((q+1:ℕ):ℝ)*Real.log z - (Real.log z)^2) := by
      rw [Real.exp_sub,Real.exp_nat_mul,Real.exp_log h0,div_eq_mul_inv,Real.exp_neg]
    _ ≤ 1 := Real.exp_le_one_iff.mpr (sub_nonpos.mpr (by
      simpa only [pow_two] using mul_le_mul_of_nonneg_right hlog hl))

/-- The original preclock selector can buy all three inequalities at the same
fine temperature, for any already fixed shape-specific radius, gate and fee. -/
theorem stage (r : ℕ) (gate : ℝ) (hg : 0 < gate) (C : ℝ) (q : ℕ) :
    ∀ᶠ z : ℝ in atTop, (Real.sqrt z)⁻¹*(Real.log z)^12 ≤ gate ∧
      2*r < 100*(1+radiusB z) ∧ C*Real.exp (-(Real.log z)^2) ≤ (z^q)⁻¹ := by
  filter_upwards [cooling.eventually (ge_mem_nhds hg),Work.E01.radiusB_tendsto.eventually_ge_atTop (2*r),
    rare C q] with z hcool hr hrare
  exact ⟨hcool,by omega,hrare⟩

theorem before (G : Gauge) (L : Lattice.Side) (r : ℕ) (gate : ℝ) (hg : 0 < gate)
    (C : ℝ) (q : ℕ) :
    ∀ᶠ x : ℝ in atTop, let z := betaF G x L
      (Real.sqrt z)⁻¹*(Real.log z)^12 ≤ gate ∧
      2*r < 100*(1+radiusB z) ∧ C*Real.exp (-(Real.log z)^2) ≤ (z^q)⁻¹ :=
  (Work.E09.betaF_growth G L).eventually (stage r gate hg C q)

end YM.Integration.WilsonTagGateSchedule
