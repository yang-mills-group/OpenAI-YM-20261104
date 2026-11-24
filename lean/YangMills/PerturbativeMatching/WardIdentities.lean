import FormalConversion
import YangMills.StressTensor

/-! Conservation, translation and normalization equations for the perturbative stress series. -/

set_option autoImplicit false
noncomputable section

namespace YangMills.Matching.WardStress

open Function Filter Set MeasureTheory
open scoped Topology BigOperators Classical

variable {g : GaugeGroup} {B : Maxwell.Reference g}

abbrev Series (B : Maxwell.Reference g) := ℕ → Axis → Axis → B.sector 4

/-- One marked stress leg with its full series before collecting a coefficient.
The other legs and this leg all use the same field and coupling conversion. -/
def inserted (M : MSbar.Coefficients B) (S : Conversion B) (P : Series B)
    {n : ℕ} (k : ℕ) (a b : Axis) (v : Fin n → Label B) (x : Points (n+1)) : ℂ :=
  ∑ j : Fin (k+1), S.correlation M (k-j.val) (Fin.cons ⟨4, P j.val a b⟩ v) x

def fluxIntegrand (M : MSbar.Coefficients B) (S : Conversion B) (P : Series B)
    {n : ℕ} (k : ℕ) (v : Fin (n+1) → Label B) (φ : WilsonFamily.SeparatedTest (n+1))
    (χ : Spacetime → ℝ) (a b : Axis) (z : Spacetime × Points (n+1)) : ℂ :=
  φ z.2 * ((Maxwell.partialD a χ z.1 : ℝ) : ℂ) *
    inserted M S P k a b v (Ward.prepend z.1 z.2)

/-- These tests use only the prescribed graph coefficients, conversion and
Maxwell coordinates. A zero one-point fixes the vacuum ambiguity at each
degree. The leading free metric stress has the translation-normalized sign. -/
structure Determined (M : MSbar.Coefficients B) (S : Conversion B) (P : Series B) : Prop where
  leading (a b : Axis) : P 0 a b = B.stress a b
  symmetric (k : ℕ) (a b : Axis) : P k a b = P k b a
  signedAxes (k : ℕ) (σ : Equiv.Perm Axis) (sign : Axis → ℝ)
      (U : Spacetime ≃ₗᵢ[ℝ] Spacetime)
      (hsign : ∀ a, sign a = 1 ∨ sign a = -1)
      (hU : ∀ a, U (EuclideanSpace.single a 1) = sign a • EuclideanSpace.single (σ a) 1)
      (a b : Axis) :
    RelatedByAxes B σ sign U (P k a b).val
      (((sign a * sign b : ℝ) : ℂ) • (P k (σ a) (σ b)).val)
  vacuum (k : ℕ) (a b : Axis) (φ : WilsonFamily.SeparatedTest 1) :
    let f := fun x => φ x * inserted M S P k a b (fun i : Fin 0 => Fin.elim0 i) x
    Integrable f ∧ (∫ x, f x) = 0
  conservation {n : ℕ} (k : ℕ) (b : Axis) (v : Fin n → Label B)
      (φ : WilsonFamily.SeparatedTest (n+1)) :
    let f := fun (a : Axis) (x : Points (n+1)) =>
      Ward.firstDerivative a (fun y => φ y) x * inserted M S P k a b v x
    (∀ a, Integrable (f a)) ∧ (∑ a : Axis, ∫ x, f a x) = 0
  translation {n : ℕ} (k : ℕ) (b : Axis) (v : Fin (n+1) → Label B)
      (φ : WilsonFamily.SeparatedTest (n+1)) (χ : Spacetime → ℝ)
      (window : ∀ x ∈ tsupport (fun y => φ y), Ward.Window x χ) :
    let rhs := fun x => Ward.firstDerivative b (fun y => φ y) x * S.correlation M k v x
    Integrable rhs ∧ (∀ a, Integrable (fluxIntegrand M S P k v φ χ a b)) ∧
      -(∑ a : Axis, ∫ z, fluxIntegrand M S P k v φ χ a b z) = -(∫ x, rhs x)

end YangMills.Matching.WardStress
