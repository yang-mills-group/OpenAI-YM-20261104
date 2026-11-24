import YangMills.CorrelationHierarchy

/-! Translation and rotation Ward identities for the physical stress tensor. -/
set_option autoImplicit false
noncomputable section
namespace YangMills
open Function Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius

namespace Ward
abbrev Rotation := ↥(Matrix.unitaryGroup Axis ℝ)
abbrev Generator := {A : Matrix Axis Axis ℝ // star A = -A}

/-- The ordinary orthogonal one-parameter subgroup with generator `A`. -/
def rotation (A : Generator) (t : ℝ) : Rotation :=
  ⟨NormedSpace.exp (t • A.val), by
    letI : NormedAlgebra ℚ (Matrix Axis Axis ℝ) := .restrictScalars ℚ ℝ _
    apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
    change star (t • A.val) = -(t • A.val)
    rw [star_smul, star_trivial, A.property, smul_neg]⟩

def rotated {n : ℕ} (R : Rotation) (x : Points n) : Points n :=
  WithLp.toLp 2 fun i => Matrix.toEuclideanLin R.val (x i)

def prepend {n : ℕ} (y : Spacetime) (x : Points n) : Points (n + 1) :=
  WithLp.toLp 2 (Fin.cons y x.ofLp)

/-- A compact smooth cutoff locally equal to one at the first insertion;
all the other points lie outside its closed support. -/
def Window {n : ℕ} (x : Points (n + 1)) (χ : Spacetime → ℝ) : Prop :=
  ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ χ =ᶠ[𝓝 (x 0)] (fun _ => 1) ∧
  ∀ i : Fin n, x i.succ ∉ tsupport χ

def firstDerivative {n : ℕ} (a : Axis) (f : Points (n + 1) → ℂ) (x : Points (n + 1)) : ℂ :=
  fderiv ℝ f x (PiLp.single 2 0 (EuclideanSpace.single a 1))
end Ward

namespace Hierarchy
variable {g : GaugeGroup} {C : WilsonFamily g} (T : Hierarchy C)

/-- The stress tensor is inserted at the integration variable `y`. -/
def shellCorrelation (s : Option T.Character) {n d : ℕ} (x : Points (n + 1))
    (v : T.Field d) (q : Fin n → T.Tag) (a b : Axis) (y : Spacetime) : ℂ :=
  T.correlation s (Fin.cons ⟨4, T.stress a b⟩ (Fin.cons ⟨d, v⟩ q)) (Ward.prepend y x)

def translationFlux (s : Option T.Character) {n d : ℕ} (x : Points (n + 1))
    (v : T.Field d) (q : Fin n → T.Tag) (χ : Spacetime → ℝ) (b : Axis) : ℂ :=
  - ∑ a : Axis, ∫ y : Spacetime,
    ((Maxwell.partialD a χ y : ℝ) : ℂ) * T.shellCorrelation s x v q a b y

def rotationFlux (s : Option T.Character) {n d : ℕ} (x : Points (n + 1))
    (v : T.Field d) (q : Fin n → T.Tag) (χ : Spacetime → ℝ) (A : Ward.Generator) : ℂ :=
  - ∑ a : Axis, ∑ b : Axis, ∫ y : Spacetime,
    ((Maxwell.partialD a χ y * Matrix.toEuclideanLin A.val (y - x 0) b : ℝ) : ℂ) *
      T.shellCorrelation s x v q a b y

/-- One action on local fields implements ordinary rotations of separated configurations.
The tensor whose flux gives the Ward identities is also the tensor used in the UV test. -/
structure StressWardLaws where
  derivative (d : ℕ) (a : Axis) : T.Field d →ₗ[ℂ] T.Field (d + 1)
  derivativeInsertion (s : Option T.Character) (d : ℕ) (a : Axis) (v : T.Field d)
      {n : ℕ} (x : Points (n + 1)) (hx : x ∈ WilsonFamily.separated (n + 1))
      (q : Fin n → T.Tag) :
    T.correlation s (Fin.cons ⟨d + 1, derivative d a v⟩ q) x =
      Ward.firstDerivative a (T.correlation s (Fin.cons ⟨d, v⟩ q)) x
  act (d : ℕ) : Ward.Rotation → (T.Field d ≃ₗ[ℂ] T.Field d)
  identity (d : ℕ) (v : T.Field d) : act d 1 v = v
  composition (d : ℕ) (R S : Ward.Rotation) (v : T.Field d) :
    act d (R * S) v = act d R (act d S v)
  continuous (d : ℕ) (v : T.Field d) : Continuous (fun R => act d R v)
  covariance (s : Option T.Character) (n : ℕ) (v : Fin n → T.Tag)
      (x : Points n) (hx : x ∈ WilsonFamily.separated n) (R : Ward.Rotation) :
    T.correlation s (fun i => ⟨(v i).1, act (v i).1 R (v i).2⟩) (Ward.rotated R x) =
      T.correlation s v x
  generator (d : ℕ) (A : Ward.Generator) : T.Field d →ₗ[ℂ] T.Field d
  infinitesimal (d : ℕ) (A : Ward.Generator) (v : T.Field d) :
    HasDerivAt (fun t => act d (Ward.rotation A t) v) (generator d A v) (0 : ℝ)
  symmetric (a b : Axis) : T.stress a b = T.stress b a
  divergence (b : Axis) : ∑ a : Axis, derivative 4 a (T.stress a b) = 0
  tensor (R : Ward.Rotation) (a b : Axis) :
    act 4 R (T.stress a b) =
      ∑ i : Axis, ∑ j : Axis, ((R.val i a * R.val j b : ℝ) : ℂ) • T.stress i j
  translation (s : Option T.Character) {n d : ℕ} (x : Points (n + 1))
      (hx : x ∈ WilsonFamily.separated (n + 1)) (v : T.Field d) (q : Fin n → T.Tag)
      (χ : Spacetime → ℝ) (window : Ward.Window x χ) (b : Axis) :
    T.translationFlux s x v q χ b =
      Ward.firstDerivative b (T.correlation s (Fin.cons ⟨d, v⟩ q)) x
  rotation (s : Option T.Character) {n d : ℕ} (x : Points (n + 1))
      (hx : x ∈ WilsonFamily.separated (n + 1)) (v : T.Field d) (q : Fin n → T.Tag)
      (χ : Spacetime → ℝ) (window : Ward.Window x χ) (A : Ward.Generator) :
    T.rotationFlux s x v q χ A = T.correlation s (Fin.cons ⟨d, generator d A v⟩ q) x

end Hierarchy
end YangMills
