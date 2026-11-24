import YangMills.PerturbativeMatching.Reference
import YangMills.PerturbativeMatching.Measurement
import YangMills.PerturbativeMatching.Asymptotics

/-! Single-cluster OPE matching through a finite output dimension, at each perturbative order. -/

set_option autoImplicit false
noncomputable section

namespace YangMills.PerturbativeMatching

open Filter Matching
open scoped Topology BigOperators Classical

variable {g : GaugeGroup} {C : WilsonFamily g} {T : Hierarchy C} {B : Maxwell.Reference g}

/-- Fuse the measured inputs at radius `r` and express their physical output
through dimension `cutoff` in the same measured frame. Each coefficient multiplies
the field that represents its channel in the hierarchy's OPE. -/
def measuredOPE (measurement : Measurement B T) {n : ℕ} (r : ℝ)
    (cutoff : ℕ) (fields : Fin n → Matching.Label B) (center : Spacetime)
    (x : Points n) : B.sector cutoff :=
  (measurement.frame r cutoff).symm
    (∑ d : Fin (cutoff + 1), ∑ channel : T.Channel d.val,
      T.coefficient (measurement.inputs r fields) d.val channel (fun i => center + r • x i) center •
        measurement.includeField (Nat.le_of_lt_succ d.isLt) (T.channelField d.val channel))

/-- The physical channels included through dimension cutoff form a basis of its field space. -/
def HasChannelBasis {B : Maxwell.Reference g} (measurement : Measurement B T) : Prop :=
  ∀ cutoff : ℕ,
    ∃ basis : Module.Basis (Σ d : Fin (cutoff + 1), T.Channel d.val) ℂ (T.Field cutoff),
      ∀ (d : Fin (cutoff + 1)) (channel : T.Channel d.val),
        basis ⟨d, channel⟩ =
          measurement.includeField (Nat.le_of_lt_succ d.isLt) (T.channelField d.val channel)

/-- Order-`order` prediction in the same finite field space as the measured output. -/
def opePartialSum (reference : Reference g) {n : ℕ} (cutoff order : ℕ) (coupling : ℝ)
    (fields : Fin n → Label (maxwellReference g)) (x : Points n) : (maxwellReference g).sector cutoff :=
  ∑ k : Fin (order + 1),
    (coupling : ℂ)^k.val • reference.scheme.conversion.ope reference.coefficients cutoff k.val fields x

/-- At every output cutoff, the whole field has the prescribed series.
The smeared estimate tests every linear functional. The compact bound controls
the field itself, and the derivative bound is uniform on the dual unit ball. -/
structure OPEExpansion (reference : Reference g)
    (measurement : Measurement (maxwellReference g) T) : Prop where
  smeared (n cutoff : ℕ) (d : Fin n → ℕ) : ∃ m : ℕ,
    ∀ (v : (i : Fin n) → (maxwellReference g).sector (d i)) (center : Spacetime)
      (out : (maxwellReference g).sector cutoff →ₗ[ℂ] ℂ),
      let fields : Fin n → Label (maxwellReference g) := fun i => ⟨d i, v i⟩
      HasSmearedExpansion m measurement.coupling (fun r x => out (measuredOPE measurement r cutoff fields center x))
        (fun k x => out (reference.scheme.conversion.ope reference.coefficients cutoff k fields x))
  uniformOnCompact (n cutoff order : ℕ) (d : Fin n → ℕ) (center : Spacetime) (K : Set (Points n)) :
    IsCompact K → K ⊆ WilsonFamily.separated n →
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ r : ℝ in 𝓝[>] 0,
      ∀ (v : (i : Fin n) → (maxwellReference g).sector (d i)) (x : Points n), x ∈ K →
      let fields : Fin n → Label (maxwellReference g) := fun i => ⟨d i, v i⟩
      coefficientNorm (measuredOPE measurement r cutoff fields center x -
        opePartialSum reference cutoff order (measurement.coupling r) fields x) ≤
        A * (∏ i, coefficientNorm (v i)) * |measurement.coupling r|^(order + 1)
  shapeDerivatives (n cutoff order derivativeOrder : ℕ) (d : Fin n → ℕ) (K : Set (Points n)) :
    IsCompact K → K ⊆ WilsonFamily.separated n →
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ r : ℝ in 𝓝[>] 0,
      ∀ (v : (i : Fin n) → (maxwellReference g).sector (d i)) (center : Spacetime)
        (x : Points n), x ∈ K → ∀ out : (maxwellReference g).sector cutoff →ₗ[ℂ] ℂ,
      (∀ w, ‖out w‖ ≤ coefficientNorm w) →
      let fields : Fin n → Label (maxwellReference g) := fun i => ⟨d i, v i⟩
      ShapeDerivativeBound derivativeOrder (fun y => out (measuredOPE measurement r cutoff fields center y))
        (fun y => out (opePartialSum reference cutoff order (measurement.coupling r) fields y)) x
        (A * (∏ i, coefficientNorm (v i)) * |measurement.coupling r|^(order + 1))

end YangMills.PerturbativeMatching
