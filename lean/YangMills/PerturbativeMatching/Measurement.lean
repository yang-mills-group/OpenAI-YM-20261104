import YangMills.PerturbativeMatching.Calibration
import YangMills.PerturbativeMatching.PositionFrame
import FormalConversion
import YangMills.StressTensor

/-! The running coupling and graded coordinates of the Wilson fields on a single hierarchy. -/

set_option autoImplicit false
noncomputable section

namespace YangMills.PerturbativeMatching

open Filter MeasureTheory Matching
open scoped Topology BigOperators Classical

variable {g : GaugeGroup} {C : WilsonFamily g}

/-- The measured running coupling and the scale-dependent coordinates of the
physical fields on one continuum hierarchy. The same coordinates serve all
characters, insertions and orders. -/
structure Measurement (B : Maxwell.Reference g) (T : Hierarchy C) where
  coupling : ℝ → ℝ
  coupling_pos : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < coupling r
  oneLoop : Tendsto (fun r => coupling r * Real.sqrt (2 * oneLoopBeta B * Real.log r⁻¹))
    (𝓝[>] 0) (𝓝 1)
  frame (r : ℝ) (d : ℕ) : B.sector d ≃ₗ[ℂ] T.Field d
  frameCompatible (d e : ℕ) (v : B.sector d) (w : B.sector e) (same : v.val = w.val) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, T.toLabel d (frame r d v) = T.toLabel e (frame r e w)
  frameEquivariant : ∃ W : T.StressWardLaws, ∀ d, ∀ᶠ r : ℝ in 𝓝[>] 0,
    ∀ (σ : Equiv.Perm Axis) (sign : Axis → ℝ) (U : Spacetime ≃ₗᵢ[ℝ] Spacetime)
      (R : Ward.Rotation), (∀ a, sign a = 1 ∨ sign a = -1) →
      (∀ a, U (EuclideanSpace.single a 1) = sign a • EuclideanSpace.single (σ a) 1) →
      (∀ x, Matrix.toEuclideanLin R.val x = U x) → ∀ v w : B.sector d,
      RelatedByAxes B σ sign U v.val w.val → W.act d R (frame r d v) = frame r d w
  unitInsertion (d : ℕ) (v : B.sector d) (unitField : v.val = 1) : ∀ᶠ r : ℝ in 𝓝[>] 0,
    ∀ (phase : Option T.Character) (n : ℕ) (fields : Fin n → T.Tag) (x : Points (n+1)),
      x ∈ WilsonFamily.separated _ →
        T.correlation phase (Fin.cons ⟨d, frame r d v⟩ fields) x =
        T.correlation phase fields (WithLp.toLp 2 fun i => x.ofLp i.succ)
  includeField {d e : ℕ} : d ≤ e → T.Field d →ₗ[ℂ] T.Field e
  label_includeField {d e : ℕ} (h : d ≤ e) (v : T.Field d) :
    T.toLabel e (includeField h v) = T.toLabel d v
  correlation_includeField {d e : ℕ} (h : d ≤ e) (v : T.Field d) (phase : Option T.Character)
      (n : ℕ) (fields : Fin n → T.Tag) (x : Points (n+1)) (hx : x ∈ WilsonFamily.separated _) :
    T.correlation phase (Fin.cons ⟨e, includeField h v⟩ fields) x =
      T.correlation phase (Fin.cons ⟨d, v⟩ fields) x
  correlationMultilinear (phase : Option T.Character) (n : ℕ) (d : Fin n → ℕ)
      (x : Points n) (hx : x ∈ WilsonFamily.separated n) :
    ∃ L : MultilinearMap ℂ (fun i => T.Field (d i)) ℂ, ∀ v,
      T.correlation phase (fun i => ⟨d i, v i⟩) x = L v

variable {B : Maxwell.Reference g} {T : Hierarchy C}

def Measurement.inputs (measurement : Measurement B T) {n : ℕ}
    (r : ℝ) (fields : Fin n → Label B) : Fin n → T.Tag :=
  fun i => ⟨(fields i).1, measurement.frame r (fields i).1 (fields i).2⟩

/-- The position frame fixes the measured coupling before the field conversion.
Integrability is required at each positive radius. The coupling identity holds at every radius. -/
structure FrameCalibration (scheme : PositionScheme g)
    (measurement : Measurement (maxwellReference g) T)
    (positionFrame : MSbar.PositionFrames T (maxwellReference g)) : Prop where
  normalized : MSbar.PositionNormalized T scheme.prescription positionFrame
  locallyUnique : MSbar.PositionLocallyUnique T scheme.prescription positionFrame
  unit : MSbar.PositionUnital T positionFrame
  nested : MSbar.PositionNested T positionFrame
  real : MSbar.PositionReal T positionFrame
  triangleIntegrable (r : ℝ) (positive : 0 < r) :
    let moment := MSbar.positionMoment T positionFrame r 6 (n := 3)
    Integrable (fun x => scheme.prescription.triangle.profile x *
      scheme.prescription.triangle.connected moment x)
  coupling (r : ℝ) : measurement.coupling r =
    scheme.prescription.triangle.measure (MSbar.positionMoment T positionFrame r 6 (n := 3)) /
      scheme.prescription.triangle.cT
  fields (d : ℕ) : ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ v,
    measurement.frame r d v = positionFrame r d (scheme.adjustment.value d (measurement.coupling r) v)

end YangMills.PerturbativeMatching
