import YangMills.CorrelationHierarchy

/-! The filtered field space and the Wightman reconstruction of each vacuum sector. -/
set_option autoImplicit false
noncomputable section
namespace YangMills

open Function Filter Set MeasureTheory
open scoped Topology BigOperators InnerProductSpace Distributions Classical ContDiff

namespace Reconstruction
variable {g : GaugeGroup} {C : WilsonFamily g}

/-- The finite grades present a single filtered space of physical labels. Each
separated moment, in the Wilson mixture and at each character, is multilinear
on that space. In particular its value is independent of the presenting grades. -/
structure TableLaws (T : Hierarchy C) : Prop where
  filtration : Monotone (fun d => LinearMap.range (T.toLabel d))
  unitInGrade (d : ℕ) : T.toLabel 4 T.unitAtFour ∈ LinearMap.range (T.toLabel d)
  multilinear (s : Option T.Character) (n : ℕ) (x : Points n)
      (separated : x ∈ WilsonFamily.separated n) :
    ∃ moment : MultilinearMap ℂ (fun _ : Fin n => T.labels.carrier) ℂ,
      ∀ v : Fin n → T.Tag, T.correlation s v x =
        moment (fun i => T.toLabel (v i).1 (v i).2)
  empty (s : Option T.Character) (v : Fin 0 → T.Tag) (x : Points 0) :
    T.correlation s v x = 1
  unit (s : Option T.Character) {n : ℕ} (v : Fin (n+1) → T.Tag)
      (x : Points (n+1)) (separated : x ∈ WilsonFamily.separated (n+1))
      (k : Fin (n+1)) (hk : T.toLabel (v k).1 (v k).2 = T.toLabel 4 T.unitAtFour) :
    T.correlation s v x = T.correlation s (v ∘ k.succAbove)
      (WithLp.toLp 2 (x.ofLp ∘ k.succAbove))

abbrev JointTest (n : ℕ) := SchwartzMap (Points n) ℂ

/-- With time last, the native Minkowski stress is −ζₐζᵦ times the Euclidean
Ward tensor, where ζ is −i on time and 1 on each spatial axis. -/
def wickAxis (a : Axis) : ℂ := if a = timeAxis then -Complex.I else 1

def minkowskiStress (T : Hierarchy C) (a b : Axis) : T.labels.carrier :=
  T.toLabel 4 ((-wickAxis a * wickAxis b) • T.stress a b)

open scoped Matrix.Norms.Frobenius

def lorentzMatrix (p : ProperLorentz) : Matrix Axis Axis ℝ :=
  fun a b => p.val.val (EuclideanSpace.single b 1) a

def affineVelocity (t : Spacetime) (V : Matrix Axis Axis ℝ) (x : Spacetime) (a : Axis) : ℝ :=
  t a + ∑ j, V a j * x j

/-- The continued grade-four stress implements the infinitesimal action of the
phase's Poincaré representation on its common field domain at finite cutoff. -/
structure ContinuedStress (T : Hierarchy C) {H : HilbertSpace}
    (A : WightmanTheory H T.labels) : Prop where
  symmetric (a b : Axis) :
    A.fields.field (minkowskiStress T a b) = A.fields.field (minkowskiStress T b a)
  tensor (p : A.poincare.Symmetry) (a b : Axis) :
    A.poincare.onLabels p (minkowskiStress T a b) =
      ∑ i, ∑ j, (((lorentzMatrix (A.poincare.coordinates p).1 i a *
        lorentzMatrix (A.poincare.coordinates p).1 j b : ℝ) : ℂ)) • minkowskiStress T i j
  conserved (b : Axis) (m : TestFunction) :
    ∃ dm : Axis → TestFunction,
      (∀ a x, dm a x = -Maxwell.partialD a (fun y => m y) x) ∧
      ∑ a, ((if a = timeAxis then 1 else -1 : ℝ) : ℂ) •
        A.fields.field (minkowskiStress T a b) (dm a) = 0
  implements (d : ℕ) (B : T.Field d) (γ : ℝ → ProperLorentz) (h0 : (γ 0).val = 1)
      (V : Matrix Axis Axis ℝ) (hV : HasDerivAt (fun τ => lorentzMatrix (γ τ)) V 0)
      (t : Spacetime) :
    ∃ W : ℝ → T.Field d, ∃ Wdot : T.Field d,
      (∀ τ, T.toLabel d (W τ) =
        A.poincare.onLabels (A.poincare.coordinates.symm (γ τ, 0)) (T.toLabel d B)) ∧
      HasDerivAt W Wdot 0 ∧
      ∀ (X : Set Spacetime), IsCompact X →
      ∀ (f : SchwartzMap ℝ ℂ), HasCompactSupport ⇑f →
        (∀ τ, ((f τ).re : ℂ) = f τ) → (∫ τ, f τ) = 1 →
      ∀ (c : SchwartzMap Space ℂ), HasCompactSupport ⇑c →
        (∃ o : Space, ∃ R : ℝ, 0 < R ∧ EqOn ⇑c (fun _ => 1) (Metric.ball o R) ∧
          ∀ x : Spacetime, time x ∈ tsupport f → spatial x ∉ Metric.ball o R →
            ∀ z ∈ X, x - z ∈ spacelike) →
        ∀ (m : TestFunction), tsupport m ⊆ X →
        ∃ J D : Axis → TestFunction,
          (∀ a x, J a x = (affineVelocity t V x a : ℂ) * (c (spatial x) * f (time x))) ∧
          (∀ a x, D a x = -Maxwell.partialD a (fun y => (affineVelocity t V y a : ℂ) * m y) x) ∧
          let charge := ∑ b, A.fields.field (minkowskiStress T timeAxis b) (J b)
          let field := A.fields.field (T.toLabel d B) m
          Complex.I • (charge.comp field - field.comp charge) =
            A.fields.field (T.toLabel d Wdot) m +
              ∑ a, A.fields.field (T.toLabel d B) (D a)

/-- One character's tube and joint tempered boundary, both multilinear on the
physical field labels. Tensor tests identify the boundary with the positive Hilbert
space vacuum functional of the same Wightman theory. -/
structure PhaseSource (T : Hierarchy C) (i : T.Character)
    (H : HilbertSpace) (A : WightmanTheory H T.labels) where
  axioms : A.Axioms
  faithful : A.fields.Faithful
  translations (x : Spacetime) (v : T.labels.carrier) :
    A.poincare.onLabels (A.poincare.pureTranslation x) v = v
  commonAdjoint : A.adjointLabel = T.theory.adjointLabel
  unitOperator (f : TestFunction) :
    A.fields.field (T.toLabel 4 T.unitAtFour) f =
      (∫ x, f x) • LinearMap.id (R := ℂ)
  stressAdjoint (a b : Axis) :
    A.adjointLabel (minkowskiStress T a b) = minkowskiStress T a b
  traceAdjoint : A.adjointLabel (T.toLabel 4 T.stressTrace) = T.toLabel 4 T.stressTrace
  centeredAdjoint : A.adjointLabel (T.toLabel 4 T.centeredTrace) = T.toLabel 4 T.centeredTrace
  wave (n : ℕ) : Hierarchy.ComplexTimes n → Hierarchy.SpatialPoints n →
    MultilinearMap ℂ (fun _ : Fin n => T.labels.carrier) ℂ
  surface (n : ℕ) : MultilinearMap ℂ (fun _ : Fin n => T.labels.carrier)
    (JointTest n →L[ℂ] ℂ)
  continuous (n : ℕ) (v : Fin n → T.labels.carrier) :
    ContinuousOn (fun p : Hierarchy.ComplexTimes n × Hierarchy.SpatialPoints n =>
      wave n p.1 p.2 v) (Hierarchy.orderedTube n ×ˢ univ)
  holomorphic (n : ℕ) (v : Fin n → T.labels.carrier) (space : Hierarchy.SpatialPoints n) :
    DifferentiableOn ℂ (fun z => wave n z space v) (Hierarchy.orderedTube n)
  euclidean (n : ℕ) (v : Fin n → T.Tag) (x : Points n)
      (ordered : StrictMono fun k => time (x k)) :
    wave n (Hierarchy.imaginaryTimes x) (Hierarchy.spatialPoints x)
      (fun k => T.toLabel (v k).1 (v k).2) = T.correlation (some i) v x
  sliceGrowth (n : ℕ) (v : Fin n → T.labels.carrier) :
    ∃ m : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ (height : Fin n → ℝ) (gap : ℝ),
      gap ∈ Ioc 0 1 → (∀ a b : Fin n, a < b → gap ≤ height b - height a) →
      ∀ x : Points n,
        ‖wave n (Hierarchy.complexShift 1 height x) (Hierarchy.spatialPoints x) v‖ ≤
          K * gap⁻¹ ^ m
  integrable (n : ℕ) (v : Fin n → T.labels.carrier) (height : Fin n → ℝ)
      (ordered : StrictMono height) (r : ℝ) (positive : 0 < r) (f : JointTest n) :
    Integrable (fun x : Points n =>
      wave n (Hierarchy.complexShift r height x) (Hierarchy.spatialPoints x) v * f x)
  boundary (n : ℕ) (v : Fin n → T.labels.carrier) (height : Fin n → ℝ)
      (ordered : StrictMono height) (f : JointTest n) :
    Tendsto (fun r : ℝ => ∫ x : Points n,
      wave n (Hierarchy.complexShift r height x) (Hierarchy.spatialPoints x) v * f x)
      (𝓝[>] 0) (𝓝 (surface n v f))
  tensor (n : ℕ) (v : Fin n → T.labels.carrier) (tests : Fin n → TestFunction) :
    ∃ f : JointTest n, (∀ x, f x = Hierarchy.tensorTest tests x) ∧
      surface n v f = A.fields.vacuumExpectation v tests

/-- Wightman reconstruction in every phase, with the selected theory and its continuation identified on the same hierarchy. -/
structure Phases (T : Hierarchy C) where
  phaseTheory : T.Character → Σ H : HilbertSpace, WightmanTheory H T.labels
  continuedStress (i : T.Character) : ContinuedStress T (phaseTheory i).2
  source (i : T.Character) : PhaseSource T i (phaseTheory i).1 (phaseTheory i).2
  selectedTheory : phaseTheory T.selected = ⟨T.H, T.theory⟩
  selectedTube (n : ℕ) (v : Fin n → T.Tag) (z : Hierarchy.ComplexTimes n)
      (ordered : z ∈ Hierarchy.orderedTube n) (space : Hierarchy.SpatialPoints n) :
    (source T.selected).wave n z space (fun i => T.toLabel (v i).1 (v i).2) =
      T.continuation v z space
  characterContinuity (n : ℕ) (v : Fin n → T.labels.carrier) (f : JointTest n) :
    Continuous (fun i => (source i).surface n v f)

end Reconstruction
end YangMills
