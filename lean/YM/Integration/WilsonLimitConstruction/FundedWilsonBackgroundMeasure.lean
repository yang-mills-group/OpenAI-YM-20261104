import YM.Integration.WilsonLimitConstruction.FundedWilsonBackgroundEnvelope

/-! The Taylor weight evaluated at its translated physical background.
Its exact comparison is the original Wilson weight at the integration
variable. The prediction kernels can therefore keep that very variable. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedWilsonBackgroundMeasure

open Function Filter MeasureTheory Lattice Wilson RG Exterior WilsonStartup
open FundedWilsonAtlas FundedWilsonBackgroundAction FundedWilsonBackgroundEnvelope
open scoped Classical Topology ContDiff BigOperators Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {G : Gauge} {n : Side}

theorem polynomial (d : ℕ) (a : Quad.Dir G) :
    Continuous (fun X : Quad.Space G => Work.G05.blockTaylor d
      (FundedWilsonBackgroundTail.action X) a) := by
  simp only [Work.G05.blockTaylor,Finset.sum_apply,Tensor.diagonal,Tensor.coeff,
    smul_apply]
  apply continuous_finsetSum
  intro j _
  have hd : Continuous (fun X : Quad.Space G => iteratedFDeriv ℝ j
      (FundedWilsonBackgroundTail.action X) (0 : Quad.Dir G)) :=
    (contDiff_partial (FundedWilsonBackgroundTail.action (G:=G)) (FundedWilsonBackgroundTail.smooth G) j).continuous.comp
      (f:=fun X : Quad.Space G => (X,(0 : Quad.Dir G))) (continuous_id.prodMk continuous_const)
  have he : Continuous (fun X : Quad.Space G => iteratedFDeriv ℝ j
      (FundedWilsonBackgroundTail.action X) (0 : Quad.Dir G) (fun _ => a)) :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => Quad.Dir G) ℝ (fun _ => a)).continuous.comp hd
  exact (continuous_const (y:=(j.factorial:ℝ)⁻¹)).mul he

theorem retained_continuous (d : ℕ) (B : fieldDir G n 1) (t : ℝ) :
    Continuous (fun U : Config G n => retained d U B t) := by
  apply continuous_finsetSum
  intro i _
  have hb : Continuous (fun U : Config G n => Quad.mat (base U i)) :=
    continuous_pi fun j => G.continuous_mat.comp (continuous_apply (edges i j))
  exact (polynomial d (t • directions B i)).comp hb

def undo (B : fieldDir G n 1) (t : ℝ) (U : Config G n) := (multiplier B t)⁻¹ * U

theorem cancels (B : fieldDir G n 1) (t : ℝ) (U : Config G n) :
    increment (undo B t U) (t • collect G B) = U := by
  change multiplier B t * ((multiplier B t)⁻¹ * U) = U
  exact mul_inv_cancel_left _ _

def approximate (d : ℕ) (B : fieldDir G n 1) (t : ℝ) (U : Config G n) :=
  FundedWilsonBackgroundEnvelope.weight d B t (undo B t U)

theorem continuous (d : ℕ) (B : fieldDir G n 1) (t : ℝ) :
    Continuous (approximate d B t) :=
  Real.continuous_exp.comp (continuous_const.mul
    ((retained_continuous d B t).comp (f:=undo B t) (continuous_const.mul continuous_id)))

theorem relative (d : ℕ) (B : fieldDir G n 1) (t : ℝ) (U : Config G n) :
    approximate d B t U = Wilson.bare (t^2)⁻¹ U * tilt d B t (undo B t U) := by
  rw [approximate,weight_ratio,cancels]

def error (d : ℕ) (B : fieldDir G n 1) (t : ℝ) (O : Config G n → ℂ) (U : Config G n) : ℂ :=
  ((approximate d B t U - Wilson.bare (t^2)⁻¹ U : ℝ) : ℂ) * O U

theorem signed (G : Gauge) (r : ℕ) : ∃ C > 0, ∀ (n : Side) (B : fieldDir G n 1),
    (∀ i, ‖directions B i‖ ≤ 1) → ∀ t : ℝ, t ≠ 0 → ‖t‖ ≤ 1 →
    ∀ (O : Config G n → ℂ) (A : ℝ), (∀ U, ‖O U‖ ≤ A) → ∀ U,
      ‖error (r+2) B t O U‖ ≤ ((Real.exp (cost C r B t) - 1) * A) * Wilson.bare (t^2)⁻¹ U := by
  obtain ⟨C,hC,h⟩ := likelihood G r
  refine ⟨C,hC,fun n B hB t ht h₁ O A hO U => ?_⟩
  have H := (h n B hB t ht h₁ (undo B t U)).2.2
  have hz := (Wilson.bare_pos (t^2)⁻¹ U).le
  rw [error,relative,norm_mul,Complex.norm_real,←mul_sub_one,norm_mul,Real.norm_of_nonneg hz]
  calc
    _ ≤ (Wilson.bare (t^2)⁻¹ U * (Real.exp (cost C r B t)-1)) * A :=
      mul_le_mul (mul_le_mul_of_nonneg_left H hz) (hO U) (norm_nonneg _) (mul_nonneg hz ((abs_nonneg _).trans H))
    _ = _ := by ring

theorem integrable (d : ℕ) (B : fieldDir G n 1) (t : ℝ) (O : Config G n → ℂ)
    (hO : Measurable O) {A : ℝ} (hA : ∀ U, ‖O U‖ ≤ A) :
    Integrable (error d B t O) (Wilson.prior G n) := by
  have hf : Continuous (fun U : Config G n =>
      ((approximate d B t U - Wilson.bare (t^2)⁻¹ U : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp ((continuous d B t).sub (Wilson.bare_cont _))
  have hi := hf.integrable_of_hasCompactSupport (μ:=Wilson.prior G n) (HasCompactSupport.of_compactSpace _)
  exact (hi.bdd_mul (c:=A) hO.aestronglyMeasurable (Eventually.of_forall hA)).congr
    (Eventually.of_forall fun U => mul_comm _ _)

end YM.Integration.WilsonLimitConstruction.FundedWilsonBackgroundMeasure
end
