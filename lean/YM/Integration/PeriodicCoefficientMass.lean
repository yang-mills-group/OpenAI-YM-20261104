import YM.Integration.RealCoefficientProjection

/-! Periodization can identify distinct cover monomials. The triangle
inequality controls their merged coefficients without a volume or multiplicity
factor. The exact monomial weight is pulled back through the address map. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration
open scoped BigOperators

theorem mapDomain_weighted_mass_le {A B : Type*} (f : A → B)
    (x : A →₀ ℂ) (w : B → ℝ) (hw : ∀ b, 0 ≤ w b) :
    (∑ b ∈ (x.mapDomain f).support, w b * ‖x.mapDomain f b‖) ≤
      ∑ a ∈ x.support, w (f a) * ‖x a‖ := by
  classical
  have hc (b : B) : x.mapDomain f b =
      ∑ a ∈ x.support with f a = b, x a := by
    simp [Finsupp.mapDomain, Finsupp.sum,
      Finsupp.single_apply, Finset.sum_ite]
  calc
    _ = ∑ b ∈ x.support.image f, w b * ‖x.mapDomain f b‖ := by
      apply Finset.sum_subset Finsupp.mapDomain_support
      intro b _ hb
      rw [Finsupp.notMem_support_iff.mp hb, norm_zero, mul_zero]
    _ ≤ ∑ b ∈ x.support.image f,
        ∑ a ∈ x.support with f a = b, w (f a) * ‖x a‖ := by
      apply Finset.sum_le_sum
      intro b _
      rw [hc]
      calc
        _ ≤ w b * ∑ a ∈ x.support with f a = b, ‖x a‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) (hw b)
        _ = _ := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun a ha => by
            rw [(Finset.mem_filter.mp ha).2]
    _ = _ := Finset.sum_fiberwise_of_maps_to
      (fun a ha => Finset.mem_image_of_mem f ha) _

/-- A noninjective coordinate map, including torus wrapping, cannot increase
the weighted absolute coefficient mass beyond the exact cover price. -/
theorem rename_weighted_mass_le {A B : Type*} (f : A → B)
    (p : MvPolynomial A ℂ) (w : (B →₀ ℕ) → ℝ) (hw : ∀ m, 0 ≤ w m) :
    (∑ m ∈ (MvPolynomial.rename f p).support,
      w m * ‖MvPolynomial.coeff m (MvPolynomial.rename f p)‖) ≤
      ∑ m ∈ p.support, w (m.mapDomain f) * ‖MvPolynomial.coeff m p‖ := by
  exact mapDomain_weighted_mass_le (Finsupp.mapDomain f)
    (AddMonoidAlgebra.coeff p) w hw

end YM.Integration
