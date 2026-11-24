import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Analysis.Complex.Basic

/-! Exact real coefficient recovery for a conjugation-invariant polynomial.
Real part is used coefficientwise, never asserted to be a ring homomorphism. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration
variable {V : Type*}

def realPolynomial (p : MvPolynomial V ℂ) : MvPolynomial V ℝ :=
  .ofCoeff (Finsupp.mapRange Complex.re (by rfl) (AddMonoidAlgebra.coeff p))

theorem realPolynomial_coeff (p : MvPolynomial V ℂ) (d : V →₀ ℕ) :
    MvPolynomial.coeff d (realPolynomial p) = (MvPolynomial.coeff d p).re := rfl

theorem realPolynomial_reembed {p : MvPolynomial V ℂ}
    (h : MvPolynomial.map (starRingEnd ℂ) p = p) :
    MvPolynomial.map Complex.ofRealHom (realPolynomial p) = p := by
  apply (MvPolynomial.map_mapRange_eq_iff Complex.ofRealHom Complex.re (by rfl) p).2
  intro d
  apply Complex.conj_eq_iff_re.mp
  have hd := congrArg (MvPolynomial.coeff d) h
  simpa only [MvPolynomial.coeff_map] using hd

theorem realPolynomial_coeff_norm {p : MvPolynomial V ℂ}
    (h : MvPolynomial.map (starRingEnd ℂ) p = p) (d : V →₀ ℕ) :
    ‖MvPolynomial.coeff d p‖ = |MvPolynomial.coeff d (realPolynomial p)| := by
  have hd := congrArg (MvPolynomial.coeff d) (realPolynomial_reembed h)
  rw [MvPolynomial.coeff_map] at hd
  rw [← hd, Complex.ofRealHom_eq_coe, Complex.norm_real, Real.norm_eq_abs]

theorem realPolynomial_support {p : MvPolynomial V ℂ}
    (h : MvPolynomial.map (starRingEnd ℂ) p = p) :
    (realPolynomial p).support = p.support := by
  exact (MvPolynomial.support_map_of_injective (realPolynomial p)
    (f := Complex.ofRealHom) Complex.ofReal_injective).symm.trans
    (congrArg MvPolynomial.support (realPolynomial_reembed h))

/-- Every coefficient-weighted absolute mass is retained exactly. In
particular, transferring structural prices incurs no coordinate-count loss. -/
theorem realPolynomial_weighted_mass {p : MvPolynomial V ℂ}
    (h : MvPolynomial.map (starRingEnd ℂ) p = p) (w : (V →₀ ℕ) → ℝ) :
    (∑ d ∈ (realPolynomial p).support,
      w d * |MvPolynomial.coeff d (realPolynomial p)|) =
    ∑ d ∈ p.support, w d * ‖MvPolynomial.coeff d p‖ := by
  rw [realPolynomial_support h]
  exact Finset.sum_congr rfl fun d _ =>
    congrArg (w d * ·) (realPolynomial_coeff_norm h d).symm

/-- A genuine coordinate equivalence preserves every weighted coefficient
mass after realification; the monomial weight is pulled back exactly. -/
theorem realPolynomial_rename_weighted_mass {W : Type*} (e : V ≃ W)
    {p : MvPolynomial V ℂ} (h : MvPolynomial.map (starRingEnd ℂ) p = p)
    (w : (W →₀ ℕ) → ℝ) :
    (∑ d ∈ (MvPolynomial.rename e (realPolynomial p)).support,
      w d * |MvPolynomial.coeff d (MvPolynomial.rename e (realPolynomial p))|) =
    ∑ d ∈ p.support, w (d.mapDomain e) * ‖MvPolynomial.coeff d p‖ := by
  classical
  rw [MvPolynomial.support_rename_of_injective e.injective, Finset.sum_image]
  · simp_rw [MvPolynomial.coeff_rename_mapDomain e e.injective]
    exact realPolynomial_weighted_mass h _
  · intro a _ b _ hab
    exact Finsupp.mapDomain_injective e.injective hab

theorem realPolynomial_eval {p : MvPolynomial V ℂ}
    (h : MvPolynomial.map (starRingEnd ℂ) p = p) (a : V → ℝ) :
    MvPolynomial.eval (fun i => (a i : ℂ)) p =
      (MvPolynomial.eval a (realPolynomial p) : ℂ) := by
  conv_lhs => rw [← realPolynomial_reembed h]
  rw [← MvPolynomial.eval₂_eq_eval_map]
  exact (MvPolynomial.map_eval₂Hom (RingHom.id ℝ) a Complex.ofRealHom
    (realPolynomial p)).symm

end YM.Integration
