import YM.Integration.WilsonOriginalAnalyticJetSamples
import YM.Integration.WilsonPositionThermometerRunning

/-! Actual sampling radii for the fixed-jet estimate. At frequency scale s
the ith radius has logarithmic age (s/(i+1))². The Wilson running law alone
separates the rescaled measured heaters on those finite, moving radii. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalDatedJetSamples
open Filter Function Lattice Wilson RG Source Extraction Table Spec
open PhysicalNext.Repeat.Legato RG17 Trace.Pilot PhysMS Climb
open scoped BigOperators Topology

variable {G : Gauge} {warm : ℝ → ℝ}

private def radial (s : ℝ) : ℝ := Real.exp (-(s^2))

theorem radii : Tendsto radial atTop trail := by
  have ages : Tendsto (fun s : ℝ => s^2) atTop atTop := tendsto_pow_atTop (by decide)
  exact tendsto_nhdsWithin_iff.mpr
    ⟨Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp ages), Eventually.of_forall fun _ => Real.exp_pos _⟩

private theorem meter (c : Coupling G warm) :
    Tendsto (fun s : ℝ => s * warm (radial s)) atTop (𝓝 (Real.sqrt G.slopeConstant⁻¹)) := by
  have hs : Tendsto (fun s : ℝ => (s * warm (radial s))^2) atTop (𝓝 G.slopeConstant⁻¹) := by
    simpa [radial,Function.comp_def,LogV,Real.log_inv,mul_pow] using c.running.comp radii
  apply ((Real.continuous_sqrt.tendsto _).comp hs).congr'
  filter_upwards [radii.eventually c.positive, eventually_ge_atTop (0 : ℝ)] with s hw hs
  exact Real.sqrt_sq (mul_nonneg hs hw.le)

private def step {n : ℕ} (i : Fin n) : ℝ := (i.val : ℝ) + 1

def date {n : ℕ} (s : ℝ) (i : Fin n) : ℝ :=
  radial (s / step i)

private theorem one (c : Coupling G warm) {n : ℕ} (i : Fin n) :
    Tendsto (fun s : ℝ => (s : ℂ) * (warm (date s i) : ℂ)) atTop
      (𝓝 (((step i * Real.sqrt G.slopeConstant⁻¹ : ℝ) : ℂ))) := by
  have hi : 0 < step i := by dsimp [step]; positivity
  have travel : Tendsto (fun s : ℝ => s/step i) atTop atTop := by
    simpa only [div_eq_inv_mul,id_eq] using
      (Tendsto.const_mul_atTop (inv_pos.mpr hi) (tendsto_id : Tendsto id (atTop : Filter ℝ) atTop))
  have scaled := ((meter c).comp travel).const_mul (step i)
  have realPay : Tendsto (fun s : ℝ => s * warm (date s i)) atTop
      (𝓝 (step i * Real.sqrt G.slopeConstant⁻¹)) := by
    apply scaled.congr fun s => ?_
    change step i * (s / step i * warm (date s i)) = s * warm (date s i)
    field_simp [hi.ne']
  simpa only [Function.comp_def,Complex.ofReal_mul] using
    Complex.continuous_ofReal.continuousAt.tendsto.comp realPay

/-- Recover the signed heat coefficients at the actual dated positive
heater. The constant is fixed before the Fourier scale or data. -/
theorem original (hG : G.Simple) (warmPaid : Coupling G warm) (n : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ s : ℝ in atTop, ∀ (f a : Fin n → ℂ) (j : Fin n),
      ‖f j‖ ≤ |s| ^ j.val * B *
        ∑ i, (‖a i‖ + ‖a i - ∑ k : Fin n, (warm (date s i) : ℂ)^k.val * f k‖) := by
  let node : Fin n → ℂ := fun i => ((step i * Real.sqrt G.slopeConstant⁻¹ : ℝ) : ℂ)
  have hroot : 0 < Real.sqrt G.slopeConstant⁻¹ :=
    Real.sqrt_pos.mpr (inv_pos.mpr (Gauge.slopeConstant_pos hG))
  have inj : Injective node := by
    intro i j hij
    have hs : step i * Real.sqrt G.slopeConstant⁻¹ = step j * Real.sqrt G.slopeConstant⁻¹ :=
      Complex.ofReal_injective hij
    have hsteps := mul_right_cancel₀ hroot.ne' hs
    apply Fin.ext
    dsimp [step] at hsteps
    exact_mod_cast (add_right_cancel hsteps)
  have hs : ∀ᶠ s : ℝ in atTop, (s : ℂ) ≠ 0 := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with s hs
    exact_mod_cast hs.ne'
  simpa only [Complex.norm_real,Real.norm_eq_abs] using
    WilsonOriginalAnalyticJetSamples.original warm date (fun s : ℝ => (s : ℂ)) hs node inj (one warmPaid)

end YM.Integration.WilsonOriginalDatedJetSamples

