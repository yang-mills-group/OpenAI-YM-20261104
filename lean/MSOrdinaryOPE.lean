import MSReference

/-! The ordinary perturbative OPE is determined by inserting its output field
in the same continuum correlation functions with arbitrary exterior fields.
The coefficients at unit relative length are read from polynomials in minus
the logarithm of the length. All positions here are relative to the fusion
center. -/
set_option autoImplicit false
noncomputable section
namespace YangMills.MSbar.Ordinary

open Filter Set
open scoped Topology BigOperators Classical

variable {g : GaugeGroup} (B : Maxwell.Reference g)
abbrev Label := Σ d, B.sector d
abbrev Correlation := (n k : ℕ) → (Fin n → Label B) → Points n → ℂ
abbrev OPE := (n h k : ℕ) → (Fin n → Label B) → Points n → B.sector h

/-- At exact output weight w and perturbative order k the Wilson coefficient is a homogeneous
polynomial field depending on log scale t and relative positions x. -/
abbrev WilsonCoefficients (n : ℕ) := (w k : ℕ) → ℝ → Points n → B.sector w

def homogeneous (w : ℕ) (p : B.toCoordinates.Pol) : Prop :=
  ∀ m ∈ p.support, Finsupp.weight (fun i : B.toCoordinates.Key => i.1 + 2) m = w

private def appendPoints {n m : ℕ} (x : Points n) (y : Points m) : Points (n + m) :=
  WithLp.toLp 2 (Fin.append x.ofLp y.ofLp)

/-- Coefficient k in the product of the OPE series with the exterior
correlation series. The spectator positions stay fixed while the cluster
shrinks by exp(-t). Every retained output has its own engineering power. -/
def truncation (A : Correlation B) {n m : ℕ} (p : WilsonCoefficients B n)
    (e h k : ℕ) (b : Fin m → Label B) (t : ℝ) (x : Points n) (y : Points m) : ℂ :=
  ∑ w : Fin (h + 1), ∑ j : Fin (k + 1),
    (Real.exp (((e : ℝ) - (w.val : ℝ)) * t) : ℂ) *
      A (m + 1) (k - j.val) (Fin.cons ⟨w.val, p w.val j.val t x⟩ b)
        (WithLp.toLp 2 (Fin.cons 0 y.ofLp))

/-- Each field coordinate is polynomial in the log scale, with uniformly bounded
degree at each perturbative order. It vanishes on collisions. The exterior
estimate tests the entire residual, uniformly on both separated compacts. -/
structure ExteriorExpansion (A : Correlation B) {n : ℕ}
    (a : Fin n → Label B) (p : WilsonCoefficients B n) : Prop where
  grade (w k t x) : homogeneous B w (p w k t x).val
  collision (w k t x) (hx : x ∉ separated n) : p w k t x = 0
  polynomial (w k : ℕ) (u : B.toCoordinates.Key →₀ ℕ) :
    ∃ D : ℕ, ∀ x, ∃ q : Polynomial ℂ, q.natDegree ≤ D ∧
      ∀ t : ℝ, MvPolynomial.coeff u (p w k t x).val = q.eval (t : ℂ)
  continuous (w k : ℕ) (t : ℝ) (u : B.toCoordinates.Key →₀ ℕ) :
    ContinuousOn (fun x => MvPolynomial.coeff u (p w k t x).val) (separated n)
  bound (K : Set (Points n)) (hK : IsCompact K) (hx : K ⊆ separated n)
      (w k : ℕ) (u : B.toCoordinates.Key →₀ ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∃ L : ℕ, ∀ᶠ t : ℝ in atTop, ∀ x ∈ K,
      ‖MvPolynomial.coeff u (p w k t x).val‖ ≤ c * (1 + t)^L
  exterior (K : Set (Points n)) (hK : IsCompact K) (hx : K ⊆ separated n)
      (m : ℕ) (b : Fin m → Label B) (E : Set (Points m)) (hE : IsCompact E)
      (hy : ∀ y ∈ E, WithLp.toLp 2 (Fin.cons (0 : Spacetime) y.ofLp) ∈ separated (m + 1))
      (h k : ℕ) :
    let e := ∑ i, (a i).1
    ∃ c : ℝ, 0 < c ∧ ∃ L : ℕ, ∀ᶠ t : ℝ in atTop, ∀ x ∈ K, ∀ y ∈ E,
      ‖A (n + m) k (Fin.append a b) (appendPoints (Real.exp (-t) • x) y) -
        truncation B A p e h k b t x y‖ ≤
          c * (1 + t)^L * Real.exp (((e : ℝ) - (h : ℝ) - 1) * t)

/-- The OPE on finite sums of homogeneous fields is the multilinear
extension of its exterior characterization. A change of cutoff used to
present an input leaves the underlying polynomial field unchanged. -/
structure Valid (A : Correlation B) (O : OPE B) : Prop where
  multilinear (n h k : ℕ) (d : Fin n → ℕ) (x : Points n) :
    ∃ F : MultilinearMap ℂ (fun i => B.sector (d i)) (B.sector h),
      ∀ v, O n h k (fun i => ⟨d i, v i⟩) x = F v
  sameInputs (n h k : ℕ) (a b : Fin n → Label B) (x : Points n)
      (equal : ∀ i, (a i).2.val = (b i).2.val) : O n h k a x = O n h k b x
  collision (n h k : ℕ) (a : Fin n → Label B) (x : Points n)
      (hx : x ∉ separated n) : O n h k a x = 0
  homogeneousWord (n : ℕ) (a : Fin n → Label B)
      (ha : ∀ i, homogeneous B (a i).1 (a i).2.val) :
    ∃ p : WilsonCoefficients B n, ExteriorExpansion B A a p ∧
      (∀ q, ExteriorExpansion B A a q → q = p) ∧
      ∀ h k x, (O n h k a x).val = ∑ w : Fin (h + 1), (p w.val k 0 x).val

/-- A single full OPE reader must exist and be determined by the independent
correlation array. This includes every positive-weight output through every
finite horizon, as well as the scalar channel. -/
def Determined (A : Correlation B) : Prop := ∃! O : OPE B, Valid B A O

/-- Numerical reader from the uniqueness certificate. -/
def read {A : Correlation B} (certificate : Determined B A) : OPE B :=
  Classical.choose certificate

theorem read_valid {A : Correlation B} (certificate : Determined B A) :
    Valid B A (read B certificate) :=
  (Classical.choose_spec certificate).1

theorem eq_read {A : Correlation B} (certificate : Determined B A) {O : OPE B}
    (valid : Valid B A O) : O = read B certificate :=
  (Classical.choose_spec certificate).2 O valid

end YangMills.MSbar.Ordinary
