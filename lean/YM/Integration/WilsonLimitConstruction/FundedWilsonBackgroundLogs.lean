import YM.Integration.WilsonLimitConstruction.FundedWilsonBackgroundRun
import YM.RG02.Actual.Selected

/-! Pointwise comparison of the fully integrated Wilson effective actions at
each individual coarse configuration on the original funded path. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedWilsonBackgroundLogs

open Function Filter MeasureTheory Lattice Wilson RG Exterior WilsonStartup
open MergeProof.Accent Extra.Trajectories PhysicalNext.Repeat.Legato
open WilsonCouplingTransport FundedWilsonAtlas FundedWilsonBackgroundEnvelope
open scoped Topology Classical BigOperators
variable {G : Gauge}

theorem monotone (C : Family G) (p N : ℕ) (β : ℕ → ℝ)
    (x w : Config G (C.side N p) → ℝ)
    (hx : Integrable x (Wilson.prior G _)) (hw : Integrable w (Wilson.prior G _))
    (h : ∀ U, x U ≤ w U) {i : ℕ} (hi : i ≤ N) :
    ∀ V, carry C p N β x i hi V ≤ carry C p N β w i hi V := by
  induction hi using Nat.decreasingInduction with
  | self => simpa only [WilsonCouplingTransport.top] using h
  | of_succ m hm ih =>
    intro V
    rw [WilsonCouplingTransport.step C p N β x hm,WilsonCouplingTransport.step C p N β w hm]
    let S := C.path.levels.clock.op m p
    let k := β (m+1)
    have hS : S.IsKernel k G := C.path.levels.transition_mass ..
    exact integral_mono (StepData.push_slice hS V _ (WilsonCouplingTransport.integrable C p N β hx hm))
      (StepData.push_slice hS V _ (WilsonCouplingTransport.integrable C p N β hw hm))
      (fun U => mul_le_mul_of_nonneg_left (ih U) (S.density_positive k U V))

theorem effective (G : Gauge) (r : ℕ) : ∃ C > 0, ∀ (R : Run G) (N p : ℕ) (t : ℝ),
    t ≠ 0 → ‖t‖ ≤ 1 → (t^2)⁻¹ = R.family.beta N p →
    ∀ B : fieldDir G (R.family.side N p) 1, (∀ j, ‖directions B j‖ ≤ 1) →
    ∀ i (hi : i ≤ N) V,
      let y := carry R.family p N (R.family.path.β N p) (FundedWilsonBackgroundMeasure.approximate (r+2) B t) i hi V
      let w := (R.family.path.rep N p i).eval V
      let q := cost C r B t
      Real.exp (-q)*w ≤ y ∧ y ≤ Real.exp q * w ∧ 0 < y ∧ ‖Real.log (y/w)‖ ≤ q := by
  obtain ⟨C,hC,H⟩ := likelihood G r
  refine ⟨C,hC,fun R N p t ht h₁ hβ B hB i hi V => ?_⟩
  let X := R.family
  let b := (t^2)⁻¹
  let w := (X.path.rep N p i).eval V
  let q := cost C r B t
  let y := carry X p N (X.path.β N p) (FundedWilsonBackgroundMeasure.approximate (r+2) B t) i hi V
  have hp : 0 < w := RG02.Actual.eval_pos R.makes.wilson hi V
  have hphys (s : ℝ) : carry X p N (X.path.β N p) (fun U => s * Wilson.bare b U) i hi V = s*w := by
    rw [FundedWilsonBackgroundRun.scale]
    have hD := WilsonCouplingTransport.physical_density X R.makes N p hi
    change s * carry X p N (X.path.β N p) (Wilson.bare b) i hi V = s * (X.path.rep N p i).eval V
    rw [show b = X.beta N p from hβ]
    exact congrArg (fun z : Config G (X.side i p) → ℝ => s * z V) hD
  have hA := (FundedWilsonBackgroundMeasure.continuous (r+2) B t).integrable_of_hasCompactSupport
    (μ:=Wilson.prior G _) (HasCompactSupport.of_compactSpace _)
  have hU (U : Config G (X.side N p)) := H (X.side N p) B hB t ht h₁ (FundedWilsonBackgroundMeasure.undo B t U)
  have hw := Wilson.bare_integrable (G:=G) (n:=X.side N p) b
  have hlo : Real.exp (-q) * w ≤ y := by
    rw [←hphys]
    apply monotone X p N _ _ _ (hw.const_mul _) hA _ hi V
    intro U
    rw [FundedWilsonBackgroundMeasure.relative,mul_comm (Real.exp _)]
    exact mul_le_mul_of_nonneg_left (hU U).1 (Wilson.bare_pos b U).le
  have hhi : y ≤ Real.exp q * w := by
    rw [←hphys]
    apply monotone X p N _ _ _ hA (hw.const_mul _) _ hi V
    intro U
    rw [FundedWilsonBackgroundMeasure.relative,mul_comm (Real.exp _)]
    exact mul_le_mul_of_nonneg_left (hU U).2.1 (Wilson.bare_pos b U).le
  have hy : 0 < y := (mul_pos (Real.exp_pos _) hp).trans_le hlo
  refine ⟨hlo,hhi,hy,abs_le.mpr ⟨?_,?_⟩⟩
  · simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) ((le_div_iff₀ hp).2 hlo)
  · simpa only [Real.log_exp] using Real.log_le_log (div_pos hy hp) ((div_le_iff₀ hp).2 hhi)

end YM.Integration.WilsonLimitConstruction.FundedWilsonBackgroundLogs
end
