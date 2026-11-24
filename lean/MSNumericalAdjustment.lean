import FormalConversion

/-! Smooth representatives of the formal field adjustment, expressed using
scalar coordinates on the public Maxwell sectors. -/
set_option autoImplicit false
noncomputable section
namespace YangMills.MSbar

open Filter
open scoped Topology BigOperators Classical ContDiff

variable {g : GaugeGroup}

/-- A single numerical representative of the specified formal field change.
The choice precedes the Wilson family, the physical clock and all measured
observables. The scalar tests give its Taylor expansion to every order. -/
structure NumericalAdjustment (B : Maxwell.Reference g)
    (N : (d k : ℕ) → Module.End ℂ (B.sector d)) where
  value (d : ℕ) (t : ℝ) : Module.End ℂ (B.sector d)
  at_zero (d : ℕ) : value d 0 = LinearMap.id
  smooth (d : ℕ) (v : B.sector d) (out : B.sector d →ₗ[ℂ] ℂ) :
    ContDiffAt ℝ ∞ (fun t : ℝ => out (value d t v)) 0
  invertible (d : ℕ) : ∀ᶠ t : ℝ in 𝓝[>] 0, Function.Bijective (value d t)
  unit (t : ℝ) (ht : 0 < t) (d : ℕ) (u : B.sector d) (hu : u.val = 1) :
    value d t u = u
  nested (t : ℝ) (ht : 0 < t) (d e : ℕ) (v : B.sector d) (w : B.sector e)
      (hw : v.val = w.val) : (value d t v).val = (value e t w).val
  triangular (t : ℝ) (ht : 0 < t) (d e : ℕ) (v : B.sector d)
      (hv : Matching.Homogeneous B e v.val) :
    ∀ m ∈ ((value d t v).val - v.val).support,
      Finsupp.weight (fun i : B.toCoordinates.Key => i.1 + 2) m < e
  real (t : ℝ) (ht : 0 < t) (d : ℕ) (v : B.sector d)
      (hv : ∀ m, (MvPolynomial.coeff m v.val).im = 0) :
    ∀ m, (MvPolynomial.coeff m (value d t v).val).im = 0
  signedAxes (t : ℝ) (ht : 0 < t) (d : ℕ) (σ : Equiv.Perm Axis)
      (sign : Axis → ℝ) (U : Spacetime ≃ₗᵢ[ℝ] Spacetime)
      (hsign : ∀ a, sign a = 1 ∨ sign a = -1)
      (hU : ∀ a, U (EuclideanSpace.single a 1) = sign a • EuclideanSpace.single (σ a) 1)
      (v w : B.sector d) (hw : Matching.RelatedByAxes B σ sign U v.val w.val) :
    Matching.RelatedByAxes B σ sign U (value d t v).val (value d t w).val
  expansion (d q : ℕ) (v : B.sector d) (out : B.sector d →ₗ[ℂ] ℂ) :
    Tendsto (fun t : ℝ =>
      (out (value d t v) - ∑ k : Fin (q+1), (t : ℂ)^k.val * out (N d k.val v)) /
        (t : ℂ)^q) (𝓝[>] 0) (𝓝 0)

end YangMills.MSbar
