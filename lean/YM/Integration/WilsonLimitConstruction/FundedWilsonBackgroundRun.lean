import YM.Integration.WilsonLimitConstruction.FundedWilsonBackgroundMeasure
import YM.Integration.WilsonCouplingTransport

/-! Propagation of the sparse ultraviolet Wilson error by the original positive
blocking operations. Every pointwise denominator below is the physical density
at the same coarse configuration on the very same funded run. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedWilsonBackgroundRun

open Function Filter MeasureTheory Lattice Wilson RG Exterior WilsonStartup
open MergeProof.Accent Extra.Trajectories PhysicalNext.Repeat.Legato
open WilsonCouplingTransport FundedWilsonAtlas FundedWilsonBackgroundEnvelope
open scoped Topology Classical BigOperators
variable {G : Gauge}

/-- The literal finite blocking kernels preserve pointwise domination for
complex signed charges, including at each individual coarse configuration. -/
theorem dominated (C : Family G) (p N : ℕ) (β : ℕ → ℝ)
    (x : Config G (C.side N p) → ℂ) (w : Config G (C.side N p) → ℝ)
    (hw : Integrable w (Wilson.prior G _)) (h : ∀ U, ‖x U‖ ≤ w U) {i : ℕ} (hi : i ≤ N) :
    ∀ V, ‖carry C p N β x i hi V‖ ≤ carry C p N β w i hi V := by
  induction hi using Nat.decreasingInduction with
  | self => simpa only [WilsonCouplingTransport.top] using h
  | of_succ m hm ih =>
    intro V
    rw [WilsonCouplingTransport.step C p N β x hm, WilsonCouplingTransport.step C p N β w hm]
    let S := C.path.levels.clock.op m p
    let k := β (m+1)
    have hS : S.IsKernel k G := C.path.levels.transition_mass ..
    have hW := WilsonCouplingTransport.integrable C p N β hw hm
    apply norm_integral_le_of_norm_le (StepData.push_slice hS V _ hW)
    exact Eventually.of_forall fun U => by
      have hp := S.density_positive k U V
      rw [norm_smul,Real.norm_of_nonneg hp,smul_eq_mul]
      exact mul_le_mul_of_nonneg_left (ih U) hp

theorem scale (C : Family G) (p N : ℕ) (β : ℕ → ℝ)
    (w : Config G (C.side N p) → ℝ) (s : ℝ) {i : ℕ} (hi : i ≤ N) :
    carry C p N β (fun U => s*w U) i hi = fun V => s*carry C p N β w i hi V := by
  induction hi using Nat.decreasingInduction with
  | self => simp only [WilsonCouplingTransport.top]
  | of_succ m hm ih =>
    rw [WilsonCouplingTransport.step C p N β _ hm,WilsonCouplingTransport.step C p N β w hm,ih]
    funext V
    simp only [StepData.push,smul_eq_mul,←integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun U => mul_left_comm ..)

theorem paid (G : Gauge) (r : ℕ) : ∃ C > 0, ∀ (R : Run G) (N p : ℕ) (t : ℝ),
    t ≠ 0 → ‖t‖ ≤ 1 → (t^2)⁻¹ = R.family.beta N p →
    ∀ B : fieldDir G (R.family.side N p) 1, (∀ j, ‖directions B j‖ ≤ 1) →
    ∀ (O : Config G (R.family.side N p) → ℂ) (A : ℝ),
    Measurable O → (∀ U, ‖O U‖ ≤ A) →
    Integrable (FundedWilsonBackgroundMeasure.error (r+2) B t O) (Wilson.prior G _) ∧
    ∀ i (hi : i ≤ N) V,
      ‖carry R.family p N (R.family.path.β N p)
          (FundedWilsonBackgroundMeasure.error (r+2) B t O) i hi V‖ ≤
        ((Real.exp (cost C r B t)-1)*A) * (R.family.path.rep N p i).eval V := by
  obtain ⟨C,hC,h⟩ := FundedWilsonBackgroundMeasure.signed G r
  refine ⟨C,hC,fun R N p t ht h₁ hβ B hB O A hO hA => ?_⟩
  refine ⟨FundedWilsonBackgroundMeasure.integrable (r+2) B t O hO hA,fun i hi V => ?_⟩
  let s := (Real.exp (cost C r B t) - 1)*A
  have hw : Integrable (fun U : Config G (R.family.side N p) =>
      s * Wilson.bare (R.family.beta N p) U) (Wilson.prior G _) := (Wilson.bare_integrable _).const_mul _
  have hx (U : Config G (R.family.side N p)) :
      ‖FundedWilsonBackgroundMeasure.error (r+2) B t O U‖ ≤ s * Wilson.bare (R.family.beta N p) U := by
    simpa only [←hβ] using h (R.family.side N p) B hB t ht h₁ O A hA U
  have H := dominated R.family p N (R.family.path.β N p) _ _ hw hx hi V
  rw [scale] at H
  have hD := WilsonCouplingTransport.physical_density R.family R.makes N p hi
  exact H.trans_eq (congrArg (fun y : Config G (R.family.side i p) → ℝ => s*y V) hD)

end YM.Integration.WilsonLimitConstruction.FundedWilsonBackgroundRun
end
