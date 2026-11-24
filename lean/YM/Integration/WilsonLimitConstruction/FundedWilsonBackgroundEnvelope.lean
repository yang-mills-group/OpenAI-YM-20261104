import YM.Integration.WilsonLimitConstruction.FundedWilsonBackgroundAction

/-! Positive Wilson weights and signed marks on the original finite group.
The local bound survives any normalized fine-field measure, including one
depending on the observed kernel and its coarse endpoint. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedWilsonBackgroundEnvelope

open Function Filter MeasureTheory Lattice Wilson RG Exterior WilsonStartup
open FundedWilsonAtlas FundedWilsonSparseSupport FundedWilsonBackgroundAction
open scoped Classical Topology ContDiff BigOperators Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {G : Gauge} {n : Side}

def cost (C : ℝ) (r : ℕ) (B : fieldDir G n 1) (t : ℝ) :=
  ((6*(links B).card : ℕ) : ℝ) * (C * ‖t‖^(r+1))

def tilt (d : ℕ) (B : fieldDir G n 1) (t : ℝ) (U : Config G n) :=
  Real.exp ((t^2)⁻¹ * (physical U B t - retained d U B t))

def weight (d : ℕ) (B : fieldDir G n 1) (t : ℝ) (U : Config G n) :=
  Real.exp (-(t^2)⁻¹ * retained d U B t)

theorem weight_ratio (d : ℕ) (B : fieldDir G n 1) (t : ℝ) (U : Config G n) :
    weight d B t U = Wilson.bare (t^2)⁻¹ (increment U (t • collect G B)) * tilt d B t U := by
  rw [weight,Wilson.bare,tilt,←Real.exp_add,FundedWilsonBackgroundAction.physical]
  congr 1
  ring

private theorem exp_change {x q : ℝ} (h : ‖x‖ ≤ q) :
    |Real.exp x - 1| ≤ Real.exp q - 1 := by
  obtain ⟨hl,hu⟩ := abs_le.mp h
  apply abs_le.mpr
  constructor
  · linarith [Real.exp_le_exp.mpr hl,Real.add_one_le_exp q,Real.add_one_le_exp (-q)]
  · linarith [Real.exp_le_exp.mpr hu]

theorem likelihood (G : Gauge) (r : ℕ) : ∃ C > 0, ∀ (n : Side)
    (B : fieldDir G n 1), (∀ i, ‖directions B i‖ ≤ 1) → ∀ t : ℝ, t ≠ 0 → ‖t‖ ≤ 1 →
    ∀ U : Config G n, Real.exp (-(cost C r B t)) ≤ tilt (r+2) B t U ∧
      tilt (r+2) B t U ≤ Real.exp (cost C r B t) ∧
      |tilt (r+2) B t U - 1| ≤ Real.exp (cost C r B t) - 1 := by
  obtain ⟨C,hC,h⟩ := FundedWilsonBackgroundAction.normalized G r
  refine ⟨C,hC,fun n B hB t ht h₁ U => ?_⟩
  have H := h n U B hB t ht h₁
  obtain ⟨hl,hu⟩ := abs_le.mp H
  exact ⟨Real.exp_le_exp.mpr hl,Real.exp_le_exp.mpr hu,exp_change H⟩

theorem charged (G : Gauge) (r : ℕ) : ∃ C > 0, ∀ (n : Side)
    (B : fieldDir G n 1), (∀ i, ‖directions B i‖ ≤ 1) → ∀ t : ℝ, t ≠ 0 → ‖t‖ ≤ 1 →
    ∀ (μ : Measure (Config G n)) [IsProbabilityMeasure μ] (O : Config G n → ℂ)
      (A : ℝ), (∀ U, ‖O U‖ ≤ A) →
      ‖∫ U, ((tilt (r+2) B t U - 1 : ℝ) : ℂ) * O U ∂μ‖ ≤
        (Real.exp (cost C r B t) - 1) * A := by
  obtain ⟨C,hC,h⟩ := likelihood G r
  refine ⟨C,hC,fun n B hB t ht h₁ μ _ O A hO => ?_⟩
  have H (U : Config G n) :
      ‖((tilt (r+2) B t U - 1 : ℝ) : ℂ) * O U‖ ≤ (Real.exp (cost C r B t) - 1) * A := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    exact mul_le_mul (h n B hB t ht h₁ U).2.2 (hO U) (norm_nonneg _)
      ((abs_nonneg _).trans (h n B hB t ht h₁ U).2.2)
  simpa using norm_integral_le_of_norm_le_const (μ:=μ) (Eventually.of_forall H)

def multiplier (B : fieldDir G n 1) (t : ℝ) : Config G n :=
  fun e => G.lieExp ((t • collect G B) e)

theorem shifted_prior (B : fieldDir G n 1) (t : ℝ) (O : Config G n → ℂ) :
    (∫ U, O (increment U (t • collect G B)) ∂Wilson.prior G n) =
      ∫ U, O U ∂Wilson.prior G n := by
  haveI : (Wilson.prior G n).IsMulLeftInvariant := by unfold Wilson.prior; infer_instance
  exact (measurePreserving_mul_left (Wilson.prior G n) (multiplier B t)).integral_comp
    (MeasurableEquiv.mulLeft (multiplier B t)).measurableEmbedding O

theorem original (B : fieldDir G n 1) (t β : ℝ) (O : Config G n → ℂ)
    (hO : Integrable O (Wilson.law G n β)) :
    Wilson.moment β O = (Wilson.partition G n β : ℂ)⁻¹ *
      ∫ U, (Wilson.bare β (increment U (t • collect G B)) : ℂ) *
        O (increment U (t • collect G B)) ∂Wilson.prior G n := by
  rw [Wilson.moment_formula β O hO]
  congr 1
  exact (shifted_prior B t (fun U => (Wilson.bare β U : ℂ) * O U)).symm

end YM.Integration.WilsonLimitConstruction.FundedWilsonBackgroundEnvelope
end
