import MSReference

/-! Formal coupling and field conversion on the free curvature labels. -/
set_option autoImplicit false
noncomputable section
namespace YangMills.Matching

open Function Filter Set MeasureTheory
open scoped BigOperators Topology Distributions Classical

variable {g : GaugeGroup}

/-- Matter-free one-loop coefficient in the public trace normalization.
The squared norms of the commutators compute the adjoint Casimir. -/
def oneLoopBeta (B : Maxwell.Reference g) : ℝ :=
  let E (i : Fin B.m) := B.matrix (EuclideanSpace.single i 1)
  let bracket (i j : Fin B.m) := E i * E j - E j * E i
  let casimir := (∑ i : Fin B.m, ∑ j : Fin B.m, -((bracket i j * bracket i j).trace).re) /
    (((g.n + 1 : ℕ) : ℝ) * (B.m : ℝ))
  11 * casimir / (48 * Real.pi ^ 2)

abbrev Label (B : Maxwell.Reference g) := Σ d, B.sector d

/-- Exact engineering degree, as distinct from cutoff membership. -/
def Homogeneous (B : Maxwell.Reference g) (h : ℕ) (p : B.toCoordinates.Pol) : Prop :=
  ∀ m ∈ p.support, Finsupp.weight (fun i : B.toCoordinates.Key => i.1 + 2) m = h

/-- Simultaneous action of a signed coordinate permutation on all curvature
indices and derivative directions. This is expressed on shell jets, independently
of any chosen basis or interacting fields. -/
def RelatedByAxes (B : Maxwell.Reference g) (σ : Equiv.Perm Axis) (sign : Axis → ℝ)
    (U : Spacetime ≃ₗᵢ[ℝ] Spacetime) (p q : B.toCoordinates.Pol) : Prop :=
  ∀ A A' : B.toCoordinates.Tower,
    (∀ j a b (v : Fin j → Spacetime), (A' j).val a b v =
      (sign a * sign b) • (A j).val (σ a) (σ b) (fun i => U (v i))) →
      B.toCoordinates.eval A' p = B.toCoordinates.eval A q

/-- One finite change of scheme as a formal series. Both coefficient
families act on every cutoff, preserve homogeneous weights, and describe
one pair of mutually inverse field redefinitions. -/
structure Conversion (B : Maxwell.Reference g) where
  f : ℕ → ℝ
  f_zero : f 0 = 0
  f_one : f 1 = 1
  Z (d k : ℕ) : B.sector d →ₗ[ℂ] B.sector d
  Zinv (d k : ℕ) : B.sector d →ₗ[ℂ] B.sector d
  leading (d) : Z d 0 = LinearMap.id
  nested (d e k) (p : B.sector d) (q : B.sector e) :
    p.val = q.val → (Z d k p).val = (Z e k q).val
  preservesGrade (d h k) (p : B.sector d) :
    Homogeneous B h p.val → Homogeneous B h (Z d k p).val
  preservesUnit (d k) (p : B.sector d) : p.val = 1 → Z d (k+1) p = 0
  real (d k) (p : B.sector d) : (∀ m, (MvPolynomial.coeff m p.val).im = 0) →
    ∀ m, (MvPolynomial.coeff m (Z d k p).val).im = 0
  signedAxes (d k) (σ : Equiv.Perm Axis) (sign : Axis → ℝ)
      (U : Spacetime ≃ₗᵢ[ℝ] Spacetime)
      (hsign : ∀ a, sign a = 1 ∨ sign a = -1)
      (hU : ∀ a, U (EuclideanSpace.single a 1) = sign a • EuclideanSpace.single (σ a) 1)
      (p q : B.sector d) : RelatedByAxes B σ sign U p.val q.val →
        RelatedByAxes B σ sign U (Z d k p).val (Z d k q).val
  leftInverse (d k) : (∑ i : Fin (k+1), (Zinv d i.val).comp (Z d (k-i.val))) =
    if k = 0 then LinearMap.id else 0
  rightInverse (d k) : (∑ i : Fin (k+1), (Z d i.val).comp (Zinv d (k-i.val))) =
    if k = 0 then LinearMap.id else 0

/-- Coefficient k of the j-th power of a single coupling series. -/
def couplingPower (f : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, k => if k = 0 then 1 else 0
  | j+1, k => ∑ i : Fin (k+1), f i.val * couplingPower f j (k-i.val)

variable {B : Maxwell.Reference g}

namespace Conversion
variable (S : Conversion B)

def inputs {n k : ℕ} (a : Fin n → Label B) (ν : Fin n → Fin (k+1)) :
    Fin n → Label B := fun i => ⟨(a i).1, S.Z (a i).1 (ν i).val (a i).2⟩

/-- Collect the coefficient of exactly degree k after the field and coupling
substitutions. Orders on distinct legs are summed independently. -/
def correlation (M : MSbar.Coefficients B) {n : ℕ} (k : ℕ)
    (a : Fin n → Label B) (x : Points n) : ℂ :=
  ∑ ν : Fin n → Fin (k+1), ∑ j : Fin (k+1),
    let used := ∑ i, (ν i).val
    if used ≤ k then (couplingPower S.f j.val (k-used) : ℂ) *
      M.correlation n j.val (S.inputs a ν) x else 0

/-- Apply the inverse field series to the entire finite-horizon OPE output
before truncation. The extra perturbative index is the degree on this output leg. -/
def ope (M : MSbar.Coefficients B) {n : ℕ} (h k : ℕ)
    (a : Fin n → Label B) (x : Points n) : B.sector h :=
  ∑ ν : Fin n → Fin (k+1), ∑ j : Fin (k+1), ∑ b : Fin (k+1),
    let used := b.val + ∑ i, (ν i).val
    if used ≤ k then (couplingPower S.f j.val (k-used) : ℂ) •
      S.Zinv h b.val (M.ope n h j.val (S.inputs a ν) x) else 0
end Conversion

end YangMills.Matching
