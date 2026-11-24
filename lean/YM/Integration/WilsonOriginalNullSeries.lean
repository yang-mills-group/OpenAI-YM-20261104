import YM.Integration.WilsonOriginalNullContraction

/-! Absolute convergence needed to pass one original countable regular
inventory through the single physical Haar kernel, with its true vacuum. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalNullSeries
open Function Filter Lattice Wilson RG Source Labels MeasureTheory Extra.Histories Next.Foundations
open scoped Classical Topology BigOperators
variable {G : Gauge} {n ν : Side} {d : ℕ}

theorem paid (R : Rep G n) (o : Site n) (X : ℕ → Support n) (f : ℕ → Config G n → ℂ)
    (c : ℕ → ℝ) (a : ℝ) (bill : SumBudget (fun j => R.p.mass (X j) (c j)) a)
    (shape : ∀ j, RegFit R o d (hol G) (X j) (f j)) (rows : ∀ j, R.p.supBounds o (X j) (f j) (c j))
    {σ C Λ e k : ℝ} (law : R.Lawful σ C Λ e k) :
    let entry j U := ((R.eval U:ℝ):ℂ)*masked R.p.threshold (X j) (f j) U
    Dominated entry ∧ ∀ j, Measurable (entry j) := by
  intro entry
  have envelope := R.envelope law
  obtain ⟨E,en⟩ := envelope.cost
  refine ⟨⟨fun j => E * R.p.mass (X j) (c j),bill.2.1.mul_left E,?_⟩,?_⟩
  · intro j U
    have hm : ‖masked R.p.threshold (X j) (f j) U‖ ≤ c j := by
      by_cases h : Healthy R.p.threshold (X j) U
      · rw [masked_eq _ _ _ _ h]
        exact (rows j).2 U h [] (Nat.zero_le _) (by simp)
      · rw [masked_ne _ _ _ _ h,norm_zero]; exact (rows j).1
    change ‖(R.eval U:ℂ)*_‖ ≤ _
    rw [norm_mul,Complex.norm_real]
    exact mul_le_mul (en U) (hm.trans (R.p.loMass _ _ (rows j).1)) (norm_nonneg _)
      ((norm_nonneg _).trans (en U))
  intro j
  exact (Complex.continuous_ofReal.measurable.comp envelope.meas).mul
    (masked_measurable _ _ _ (shape j).smooth.borel)

end YM.Integration.WilsonOriginalNullSeries
