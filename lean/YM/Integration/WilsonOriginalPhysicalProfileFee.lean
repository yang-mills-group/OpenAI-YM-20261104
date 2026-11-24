import YM.Integration.WilsonOriginalPurchasedMeanPrice
import YM.Integration.WilsonOriginalUniformBoxProfiles

/-! Apply a single fixed-order signed compact wage to all the original
modulations of a product pupil before choosing its perturbative order. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPhysicalProfileFee
open Filter Set MeasureTheory Finset Trace.Pilot
open WilsonOriginalUniformBoxProfiles (budget)
open WilsonOriginalGevreyWindow (window)
open WilsonOriginalFourierLattice (height)
open WilsonOriginalBoxFourierProfiles (frequency)
open WilsonOriginalModulatedProfiles (wave)
open WilsonOriginalFourierBoxIntegral (test)
open scoped Topology ContDiff BigOperators

theorem original {d : ℕ} (u : ℝ → ℝ) (f : ℝ → (Fin d → ℝ) → ℂ)
    (a : ℕ → (Fin d → ℝ) → ℂ) (l h : Fin d → ℝ) (D : ℕ)
    (originalTests : ∀ q : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ r : ℝ in trail,
      ∀ φ : Fin d → ℝ → ℂ, (∀ i, ContDiff ℝ ∞ (φ i)) →
        (∀ i t, t ∉ Icc (l i) (h i) → φ i t = 0) →
        ∀ A : ℝ, 0 ≤ A →
          (∀ o : Fin d → ℕ, (∀ i, o i ≤ D) → ∀ x : Fin d → ℝ,
            ‖∏ i, iteratedDeriv (o i) (φ i) (x i)‖ ≤ A) →
          ‖(∫ x, (∏ i,φ i (x i))*f r x) - ∑ k : Fin (q+1),
            (u r:ℂ)^k.val*(∫ x, (∏ i,φ i (x i))*a k.val x)‖ ≤ C*u r^q*A) :
    ∀ q : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ r : ℝ in trail, ∀ v : Fin d → ℤ,
      ‖(∫ x, test l h v x*f r x) - ∑ k : Fin (q+1),
        (u r:ℂ)^k.val*(∫ x, test l h v x*a k.val x)‖ ≤
        K*u r^q*(1+(height v:ℝ))^(d*D) := by
  intro q
  obtain ⟨C,nonneg,bought⟩ := originalTests q
  have positive : 0 ≤ budget d D := sum_nonneg (fun _ _ => WilsonOriginalUniformBoxProfiles.nonnegative _)
  refine ⟨C*budget d D,mul_nonneg nonneg positive,?_⟩
  filter_upwards [bought] with r paid v
  obtain ⟨_,smooth,support,order⟩ := WilsonOriginalUniformBoxProfiles.original l h v D
  let φ := fun i : Fin d => window (l i) (h i)*wave (frequency (v i))
  have price := paid φ smooth support (budget d D*(1+(height v:ℝ))^(d*D)) (by positivity) order
  apply price.trans_eq
  ring

end YM.Integration.WilsonOriginalPhysicalProfileFee
