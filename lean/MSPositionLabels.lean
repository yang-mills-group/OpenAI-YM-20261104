import Mathlib.RingTheory.PowerSeries.Basic
import MSReference
import MSPositionCubic

/-! The three insertions and the signed coupling diagnostic in the position scheme.
The leading two-form components, their color contractions, and the first-order
normalization are fixed by free Maxwell geometry and the cubic action. -/
set_option autoImplicit false
noncomputable section
namespace YangMills.MSbar.Position

open Function MeasureTheory
open scoped BigOperators Topology Classical

variable {g : GaugeGroup}

/-- In the positive orientation 0123, the chiral components are
`(F_{0,i+1} ± F_{j+1,k+1}) / √2` with `(i,j,k)` cyclic. -/
def chiralField (B : Maxwell.Reference g) (plus : Bool)
    (A : B.toCoordinates.Tower) (i : Fin 3) : Maxwell.Color B.m :=
  let F (a b : Axis) := (A 0).val a b (fun _ => 0)
  let electric := F 0 i.succ
  let magnetic := F (i+1).succ (i+2).succ
  (Real.sqrt 2)⁻¹ • (if plus then electric + magnetic else electric - magnetic)

/-- Cubic self-dual curvature contraction. The matrix trace converts the Lie
commutator to the inner product of the public color frame. -/
def cubicValue (B : Maxwell.Reference g) (A : B.toCoordinates.Tower) : ℝ :=
  let V (i : Fin 3) := B.matrix (chiralField B true A i)
  ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
    Cubic.orientation i j k * (-(V i * (V j * V k - V k * V j)).trace.re /
      ((g.n + 1 : ℕ) : ℝ))

/-- Quadratic anti-self-dual curvature contraction including its symmetry factor. -/
def quadraticValue (B : Maxwell.Reference g) (A : B.toCoordinates.Tower) : ℝ :=
  (1/2 : ℝ) * ∑ i : Fin 3, inner ℝ (chiralField B false A i) (chiralField B false A i)

/-- Both quadratic insertions have the same grade-four polynomial. All three
faces are read in the common cutoff six, including the missing-slot unit. -/
structure Triangle (B : Maxwell.Reference g) where
  T : B.sector 6
  U : B.sector 4
  UatSix : B.sector 6
  sameU : UatSix.val = U.val
  unit : B.sector 6
  unitValue : unit.val = 1
  cubic (A : B.toCoordinates.Tower) : B.toCoordinates.eval A T.val = (cubicValue B A : ℂ)
  quadratic (A : B.toCoordinates.Tower) :
    B.toCoordinates.eval A U.val = (quadraticValue B A : ℂ)
  cut : ContDiffBump (0 : Spacetime)
  profile : SeparatedTest 3

/-- Pointwise third joint cumulant for a ring of moments or of formal moment series.
All faces are evaluated jointly before applying the position test. -/
def connectedThree {R : Type*} [CommRing R] (face : Finset (Fin 3) → R) : R :=
  face Finset.univ - (face {0,1} * face {2} + face {0,2} * face {1} + face {1,2} * face {0}) +
    2 * face {0} * face {1} * face {2}

namespace Triangle
variable {B : Maxwell.Reference g} (t : Triangle B)

def labels : Fin 3 → B.sector 6 := ![t.T, t.UatSix, t.UatSix]

def face (s : Finset (Fin 3)) : Fin 3 → B.sector 6 :=
  fun i => if i ∈ s then t.labels i else t.unit

abbrev missing (s : Finset (Fin 3)) : Fin 3 → B.sector 6 := t.face s

def connected (moment : (Fin 3 → B.sector 6) → Points 3 → ℂ) (x : Points 3) : ℂ :=
  connectedThree (fun s => moment (t.face s) x)

def measure (moment : (Fin 3 → B.sector 6) → Points 3 → ℂ) : ℝ :=
  (∫ x, t.profile x * t.connected moment x).re

/-- Signed diagram normalization fixed before consulting any interacting hierarchy. -/
def cT : ℝ := ∫ x : Points 3, (t.profile x).re * bareTriangle B t.cut x

/-- Apply the cumulant to formal series before extracting the first power.
This includes all Leibniz terms on the proper faces. -/
def firstConnected (M : MSbar.Coefficients B) (x : Points 3) : ℂ :=
  PowerSeries.coeff 1 (connectedThree fun s => PowerSeries.mk fun k =>
    M.correlation 3 k (fun i => ⟨6, t.face s i⟩) x)

/-- All compact smooth profiles with this symmetry, clearance and negative
bare cubic reading are eligible, before any MS-bar predictions are evaluated. -/
structure Admissible : Prop where
  nonnegative (x : Points 3) : 0 ≤ (t.profile x).re
  realValue (x : Points 3) : (t.profile x).im = 0
  turns (V : Spacetime ≃ₗᵢ[ℝ] Spacetime) (x : Points 3) :
    t.profile (WithLp.toLp 2 (fun i => V (x i))) = t.profile x
  separated (x : Points 3) : x ∈ tsupport t.profile →
    ∀ i j : Fin 3, i ≠ j → max 4 (5 * t.cut.rOut) < ‖x i - x j‖
  negative : t.cT < 0

/-- The MS-bar coefficient has the full signed value prescribed by the bare
diagram. This equation must be tested on every admissible profile. -/
def RawSlopeAgrees (M : MSbar.Coefficients B) : Prop :=
  (∫ x, t.profile x * t.firstConnected M x) = (t.cT : ℂ)

end Triangle
end YangMills.MSbar.Position
