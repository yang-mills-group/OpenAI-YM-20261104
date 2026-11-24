import YM.Integration.WilsonOriginalDatedJetSamples

/-! On the chosen frequency |p|=s^12, the actual tube at a sample of
temperature u contributes exp(D/u^4-c*s^6*u). This is summably small to
every fixed order at all the finitely many original sampling radii. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalAnalyticFourierTail
open Filter Function Lattice Wilson RG Source Extraction Table Spec
open PhysicalNext.Repeat.Legato RG17 Trace.Pilot PhysMS Climb
open scoped Topology
open WilsonOriginalDatedJetSamples (date)

private theorem lower {G : Gauge} {warm : ℝ → ℝ} (hG : G.Simple) (paid : Coupling G warm)
    (n : ℕ) : ∃ a : ℝ, 0 < a ∧ ∀ᶠ s : ℝ in atTop, ∀ i : Fin n,
      0 < warm (date s i) ∧ a ≤ s * warm (date s i) := by
  let r := fun s : ℝ => Real.exp (-(s^2))
  have dates : Tendsto r atTop trail := WilsonOriginalDatedJetSamples.radii
  have squared : Tendsto (fun s : ℝ => (s * warm (r s))^2) atTop (𝓝 G.slopeConstant⁻¹) := by
    simpa [r,Function.comp_def,LogV,Real.log_inv,mul_pow] using paid.running.comp dates
  let L := Real.sqrt G.slopeConstant⁻¹
  have hL : 0 < L := Real.sqrt_pos.mpr (inv_pos.mpr (Gauge.slopeConstant_pos hG))
  have meter : Tendsto (fun s : ℝ => s * warm (r s)) atTop (𝓝 L) := by
    apply ((Real.continuous_sqrt.tendsto _).comp squared).congr'
    filter_upwards [dates.eventually paid.positive,eventually_ge_atTop (0:ℝ)] with s hp hs
    exact Real.sqrt_sq (mul_nonneg hs hp.le)
  refine ⟨L/2,half_pos hL,Filter.eventually_all.mpr fun i => ?_⟩
  let k : ℝ := (i.val : ℝ)+1
  have hk : 1 ≤ k := by exact le_add_of_nonneg_left (Nat.cast_nonneg i.val)
  have pos : 0 < k := zero_lt_one.trans_le hk
  have go : Tendsto (fun s : ℝ => s/k) atTop atTop := by
    simpa only [div_eq_inv_mul,id_eq] using
      (Tendsto.const_mul_atTop (inv_pos.mpr pos) (tendsto_id : Tendsto id (atTop : Filter ℝ) atTop))
  have base := (tendsto_order.mp meter).1 (L/2) (half_lt_self hL)
  filter_upwards [go.eventually base,(dates.comp go).eventually paid.positive,
    eventually_ge_atTop (0:ℝ)] with s hl hp hs
  exact ⟨hp,hl.le.trans (mul_le_mul_of_nonneg_right (div_le_self hs hk) hp.le)⟩

/-- The analytic Fourier estimate on the actual sampled heaters beats
every inverse power, uniformly over the finite sampling bank. -/
theorem original {G : Gauge} {warm : ℝ → ℝ} (hG : G.Simple) (paid : Coupling G warm)
    (n k : ℕ) (A D c : ℝ) (hA : 0 ≤ A) (hD : 0 ≤ D) (hc : 0 < c) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ s : ℝ in atTop, ∀ i : Fin n, let u := warm (date s i)
      s^k * (A * (u⁻¹)^2 * Real.exp (D*(u⁻¹)^4 - c*s^6*u)) ≤ ε := by
  obtain ⟨a,ha,bank⟩ := lower hG paid n
  have hca : 0 < c*a := mul_pos hc ha
  have small := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero (k+2)).const_mul (A/a^2)
  rw [mul_zero] at small
  filter_upwards [bank,eventually_ge_atTop (1:ℝ),
    eventually_ge_atTop ((D/a^4+1)/(c*a)),(tendsto_order.mp small).2 ε hε] with s hs hs1 height tail i
  let u := warm (date s i)
  obtain ⟨hu,hau⟩ := hs i
  have hu' : 0 < u := hu
  have h0 : 0 ≤ s := zero_le_one.trans hs1
  have hi : u⁻¹ ≤ s/a := (le_div_iff₀ ha).2 (calc
    u⁻¹*a ≤ u⁻¹*(s*u) := mul_le_mul_of_nonneg_left hau (inv_nonneg.mpr hu'.le)
    _ = s := by field_simp)
  have income : D/a^4 + 1 ≤ c*a*s := by simpa only [mul_comm s] using (div_le_iff₀ hca).1 height
  have exponent : D*(u⁻¹)^4 - c*s^6*u ≤ -s := by
    have positive := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (inv_nonneg.mpr hu'.le) hi 4) hD
    have spend : (D/a^4+1)*s^4 ≤ c*s^6*u := calc
      _ ≤ c*a*s*s^4 := mul_le_mul_of_nonneg_right income (pow_nonneg h0 _)
      _ = (c*s^5)*a := by ring
      _ ≤ (c*s^5)*(s*u) := mul_le_mul_of_nonneg_left hau (mul_nonneg hc.le (pow_nonneg h0 _))
      _ = c*s^6*u := by ring
    have sc : s ≤ s^4 := by calc
      s = s^1 := (pow_one _).symm
      _ ≤ s^4 := pow_le_pow_right₀ hs1 (by decide)
    rw [div_pow] at positive
    linarith only [positive,spend,sc,mul_comm (D/a^4+1) (s^4),
      show D*(s^4/a^4)=(D/a^4)*s^4 by ring]
  have expFee := Real.exp_le_exp.mpr exponent
  change s^k*(A*(u⁻¹)^2*Real.exp _) ≤ ε
  calc
    _ ≤ s^k*(A*(s/a)^2*Real.exp (-s)) := mul_le_mul_of_nonneg_left
      (mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (inv_nonneg.mpr hu'.le) hi 2) hA)
        expFee (Real.exp_nonneg _) (mul_nonneg hA (sq_nonneg _))) (pow_nonneg h0 _)
    _ = (A/a^2)*(s^(k+2)*Real.exp (-s)) := by rw [pow_add,div_pow]; ring
    _ ≤ ε := tail.le

end YM.Integration.WilsonOriginalAnalyticFourierTail

