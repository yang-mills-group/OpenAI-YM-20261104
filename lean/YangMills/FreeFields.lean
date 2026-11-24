import Mathlib.RingTheory.MvPolynomial.Basic
import YangMills.Geometry

/-! Gauge-invariant local polynomials in the free curvature and the Wick moments that determine their correlations. -/
set_option autoImplicit false
noncomputable section
namespace YangMills.Maxwell
open Function Set
open scoped BigOperators Topology InnerProductSpace Classical

abbrev Color (m : ℕ) := EuclideanSpace ℝ (Fin m)
abbrev Tensor (m j : ℕ) := ContinuousMultilinearMap ℝ (fun _ : Fin j => Spacetime) (Color m)
abbrev TwoJet (m j : ℕ) := Axis → Axis → Tensor m j

def partialD {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (a : Axis) (f : Spacetime → V) (x : Spacetime) := fderiv ℝ f x (EuclideanSpace.single a 1)

def diagonal {m j : ℕ} (A : Tensor m j) (x : Spacetime) := A (fun _ => x)

/-- Ordinary curvature derivatives commute. The two form indices are antisymmetric,
and the Taylor two-form is closed and divergence-free. -/
def OnShell {m j : ℕ} (A : TwoJet m j) : Prop :=
  (∀ a b v (σ : Equiv.Perm (Fin j)), A a b (v ∘ σ) = A a b v) ∧
  (∀ a b, A a b = - A b a) ∧
  (∀ a b c x, partialD a (diagonal (A b c)) x + partialD b (diagonal (A c a)) x +
    partialD c (diagonal (A a b)) x = 0) ∧
  ∀ b x, ∑ a, partialD a (diagonal (A a b)) x = 0

/-- Coordinates on the specified shell, in a trace-normalized color frame. -/
structure Coordinates (g : GaugeGroup) where
  m : ℕ
  matrix : Color m →ₗ[ℝ] Matrix (Fin (g.n+1)) (Fin (g.n+1)) ℂ
  colors : LinearMap.range matrix = g.lieAlgebra
  traceForm (c e : Color m) : -(matrix c * matrix e).trace.re =
    ((g.n+1 : ℕ) : ℝ) * inner ℝ c e
  shell (j : ℕ) : Submodule ℝ (TwoJet m j)
  shell_iff (j) (A : TwoJet m j) : A ∈ shell j ↔ OnShell A
  rank : ℕ → ℕ
  basis (j : ℕ) : Module.Basis (Fin (rank j)) ℝ (shell j)
  rotate (u : g.image) (j : ℕ) : shell j →ₗ[ℝ] shell j
  adjoint (u : g.image) (j) (A : shell j) (a b v) :
    matrix ((rotate u j A).val a b v) = u.val.val * matrix (A.val a b v) * star u.val.val

namespace Coordinates
variable {g : GaugeGroup} (B : Coordinates g)
abbrev Key := (j : ℕ) × Fin (B.rank j)
abbrev Pol := MvPolynomial B.Key ℂ
abbrev Tower := (j : ℕ) → B.shell j

def eval (A : B.Tower) : B.Pol →ₐ[ℂ] ℂ := MvPolynomial.aeval
  fun i => ((B.basis i.1).repr (A i.1) i.2 : ℝ)

/-- The total monomial weight counts each order-j curvature factor with weight j+2. -/
def Admissible (d : ℕ) (p : B.Pol) : Prop :=
  p ∈ MvPolynomial.restrictSupport ℂ {s | Finsupp.weight (fun i : B.Key => i.1+2) s ≤ d} ∧
  ∀ u : g.image, ∀ A : B.Tower, B.eval (fun j => B.rotate u j (A j)) p = B.eval A p

def green (x : Spacetime) : ℝ := (4 * Real.pi^2)⁻¹ * (‖x‖^2)⁻¹
def rightCurl (b k l : Axis) : Spacetime → ℝ :=
  (if k=b then partialD l green else 0) - (if l=b then partialD k green else 0)
def curvatureKernel (a b k l : Axis) :=
  partialD a (rightCurl b k l) - partialD b (rightCurl a k l)

def taylor {m : ℕ} (f : Axis → Axis → Spacetime → Color m) (j : ℕ) (x : Spacetime) :
    TwoJet m j := fun a b => (j.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ j (f a b) x

/-- Pair two coordinate probes against the differentiated double curl of the
massless propagator. The sign accounts for derivatives at the second insertion. -/
def covariance (p q : B.Key) (x y : Spacetime) : ℂ :=
  let project (j : ℕ) : TwoJet B.m j →ₗ[ℝ] B.shell j := @LinearMap.leftInverse ℝ (B.shell j) (TwoJet B.m j) _ _ _ _ _ (B.shell j).subtype
  let leg (i : B.Key) : TwoJet B.m i.1 →ₗ[ℝ] ℝ := ((B.basis i.1).coord i.2).comp (project i.1)
  let e (c : Fin B.m) : Color B.m := EuclideanSpace.single c 1
  let response (k l : Axis) (z : Spacetime) : Color B.m :=
    ∑ c, leg p (taylor (fun a b w => curvatureKernel a b k l w • e c) p.1 z) • e c
  (((-1 : ℝ)^q.1 * leg q (taylor response q.1 (x-y))) : ℝ)

abbrev Occ {n : ℕ} (W : Fin n → B.Key →₀ ℕ) :=
  {p : Fin n × B.Key × ℕ // p.2.2 < W p.1 p.2.1}
abbrev Pairing {n : ℕ} (W : Fin n → B.Key →₀ ℕ) :=
  {s : Equiv.Perm (B.Occ W) // s*s = 1 ∧ ∀ v, (s v).val.1 ≠ v.val.1}

/-- All complete cross-insertion pairings, with each edge counted once. Both
index sets are finite because each monomial has finite support. -/
def wickMonomial {n : ℕ} (x : Points n) (W : Fin n → B.Key →₀ ℕ) : ℂ :=
  ∑ᶠ s : B.Pairing W, ∏ᶠ v : B.Occ W,
    if v.val.1 < (s.val v).val.1 then
      B.covariance v.val.2.1 (s.val v).val.2.1 (x v.val.1) (x (s.val v).val.1)
    else 1

/-- The Euclidean stress tensor with its translation Ward normalization. -/
def stressValue (A : B.Tower) (a b : Axis) : ℂ :=
  let F (i j : Axis) := (A 0).val i j (fun _ => 0)
  let energy (i j : Axis) : ℝ := ∑ l, inner ℝ (F i l) (F j l)
  let trace : ℝ := ∑ i, energy i i
  show ℂ from -(↑(energy a b - (if a = b then 1 else 0 : ℝ) * (1/4) * trace) : ℂ)

end Coordinates

structure Reference (g : GaugeGroup) extends Coordinates g where
  sector (d : ℕ) : Submodule ℂ toCoordinates.Pol
  sector_iff (d p) : p ∈ sector d ↔ toCoordinates.Admissible d p
  moment {n : ℕ} (x : Points n) : MultilinearMap ℂ (fun _ : Fin n => toCoordinates.Pol) ℂ
  wick {n : ℕ} (x : Points n) (W : Fin n → toCoordinates.Key →₀ ℕ) :
    moment x (fun i => MvPolynomial.basisMonomials _ ℂ (W i)) = toCoordinates.wickMonomial x W
  stress (a b : Axis) : sector 4
  stress_eval (A : toCoordinates.Tower) (a b) :
    toCoordinates.eval A (stress a b).val = toCoordinates.stressValue A a b
  detected (d) (p : sector d) :
    (∀ n (w : Fin n → Σ e, sector e) (x : Points (n+1)), x ∈ YangMills.separated _ →
      moment x (Fin.cons p.val (fun i => (w i).2.val)) = 0) ↔ p = 0

end YangMills.Maxwell
