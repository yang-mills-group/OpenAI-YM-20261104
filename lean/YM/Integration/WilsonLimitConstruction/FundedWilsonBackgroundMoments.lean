import YM.Integration.WilsonLimitConstruction.FundedWilsonBackgroundRun

/-! On each genuine original blocking chain the signed error is the difference
of two actual integrated charged densities, including all cofactors in the
single bounded measurable observable. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedWilsonBackgroundMoments

open Function Filter MeasureTheory Lattice Wilson RG Exterior WilsonStartup
open MergeProof.Accent Extra.Trajectories PhysicalNext.Repeat.Legato
open WilsonCouplingTransport FundedWilsonAtlas FundedWilsonBackgroundEnvelope
open scoped Topology Classical BigOperators
variable {G : Gauge} {n : Side}

def mark (w : Config G n → ℝ) (O : Config G n → ℂ) (U : Config G n) : ℂ := (w U:ℂ)*O U

theorem charge (w : Config G n → ℝ) (hw : Continuous w) (O : Config G n → ℂ)
    (hO : Measurable O) {A : ℝ} (hA : ∀ U, ‖O U‖ ≤ A) : Integrable (mark w O) (Wilson.prior G n) := by
  have hi := (Complex.continuous_ofReal.comp hw).integrable_of_hasCompactSupport
    (μ:=Wilson.prior G n) (HasCompactSupport.of_compactSpace _)
  exact (hi.bdd_mul (c:=A) hO.aestronglyMeasurable (Eventually.of_forall hA)).congr
    (Eventually.of_forall fun U => mul_comm _ _)

theorem subtract (C : Family G) (p N : ℕ) (β : ℕ → ℝ)
    (x w : Config G (C.side N p) → ℂ)
    (hx : Integrable x (Wilson.prior G _)) (hw : Integrable w (Wilson.prior G _)) {i : ℕ} (hi : i ≤ N) :
    carry C p N β (x-w) i hi = carry C p N β x i hi - carry C p N β w i hi := by
  induction hi using Nat.decreasingInduction with
  | self => simp only [WilsonCouplingTransport.top]
  | of_succ m hm ih =>
    rw [WilsonCouplingTransport.step C p N β (x-w) hm,WilsonCouplingTransport.step C p N β x hm,
      WilsonCouplingTransport.step C p N β w hm,ih]
    funext V
    let S := C.path.levels.clock.op m p
    let k := β (m+1)
    have hS : S.IsKernel k G := C.path.levels.transition_mass ..
    simp only [StepData.push,Pi.sub_apply,smul_sub]
    exact integral_sub (StepData.push_slice hS V _ (WilsonCouplingTransport.integrable C p N β hx hm))
      (StepData.push_slice hS V _ (WilsonCouplingTransport.integrable C p N β hw hm))

theorem compares (C : Family G) (p N : ℕ) (β : ℕ → ℝ) (d : ℕ)
    (B : fieldDir G (C.side N p) 1) (t : ℝ) (O : Config G (C.side N p) → ℂ)
    (hO : Measurable O) {A : ℝ} (hA : ∀ U, ‖O U‖ ≤ A) {i : ℕ} (hi : i ≤ N) :
    carry C p N β (FundedWilsonBackgroundMeasure.error d B t O) i hi =
      carry C p N β (mark (FundedWilsonBackgroundMeasure.approximate d B t) O) i hi -
      carry C p N β (mark (Wilson.bare (t^2)⁻¹) O) i hi := by
  have h : FundedWilsonBackgroundMeasure.error d B t O =
      mark (FundedWilsonBackgroundMeasure.approximate d B t) O - mark (Wilson.bare (t^2)⁻¹) O := by
    funext U
    simp only [FundedWilsonBackgroundMeasure.error,mark,Pi.sub_apply,Complex.ofReal_sub,sub_mul]
  rw [h]
  exact subtract C p N β _ _ (charge _ (FundedWilsonBackgroundMeasure.continuous d B t) O hO hA)
    (charge _ (Wilson.bare_cont _) O hO hA) hi

theorem purchase (G : Gauge) (r : ℕ) : ∃ C > 0, ∀ (R : Run G) (N p : ℕ) (t : ℝ),
    t ≠ 0 → ‖t‖ ≤ 1 → (t^2)⁻¹ = R.family.beta N p →
    ∀ B : fieldDir G (R.family.side N p) 1, (∀ j, ‖directions B j‖ ≤ 1) →
    ∀ (O : Config G (R.family.side N p) → ℂ) (A : ℝ),
    Measurable O → (∀ U, ‖O U‖ ≤ A) → ∀ i (hi : i ≤ N) V,
      ‖carry R.family p N (R.family.path.β N p) (mark (FundedWilsonBackgroundMeasure.approximate (r+2) B t) O) i hi V -
        carry R.family p N (R.family.path.β N p) (mark (Wilson.bare (R.family.beta N p)) O) i hi V‖ ≤
        ((Real.exp (cost C r B t)-1)*A) * (R.family.path.rep N p i).eval V := by
  obtain ⟨C,hC,H⟩ := FundedWilsonBackgroundRun.paid G r
  refine ⟨C,hC,fun R N p t ht h₁ hβ B hB O A hO hA i hi V => ?_⟩
  have he := (H R N p t ht h₁ hβ B hB O A hO hA).2 i hi V
  rw [compares R.family p N _ _ _ _ _ hO hA hi,Pi.sub_apply,hβ] at he
  exact he

end YM.Integration.WilsonLimitConstruction.FundedWilsonBackgroundMoments
end
