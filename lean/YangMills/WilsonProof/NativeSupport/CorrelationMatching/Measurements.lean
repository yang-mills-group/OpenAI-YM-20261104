import YangMills.WilsonProof.NativeSupport.MatchingSpec
import YangMills.WilsonProof.NativeSupport.MSPhysicalAppointment

set_option autoImplicit false
noncomputable section

namespace YangMills.CorrelationMatching

open Filter MeasureTheory Matching MSbar
open scoped Topology BigOperators Classical

variable {g : GaugeGroup} {C : WilsonFamily g}

/-- The measured running coupling and the scale-dependent coordinates of the
physical fields on one continuum hierarchy. The same coordinates serve all
characters, insertions and orders. -/
structure Measurement (B : Maxwell.Reference g) (T : Hierarchy C) where
  coupling : ℝ → ℝ
  positive : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < coupling r
  oneLoop : Tendsto (fun r => coupling r * Real.sqrt (2 * oneLoopBeta B * Real.log r⁻¹))
    (𝓝[>] 0) (𝓝 1)
  frame (r : ℝ) (d : ℕ) : B.sector d ≃ₗ[ℂ] T.Field d
  nested (d e : ℕ) (v : B.sector d) (w : B.sector e) (same : v.val = w.val) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, T.toLabel d (frame r d v) = T.toLabel e (frame r e w)
  frameAxes : ∃ W : T.StressWardLaws, ∀ d, ∀ᶠ r : ℝ in 𝓝[>] 0,
    ∀ (σ : Equiv.Perm Axis) (sign : Axis → ℝ) (U : Spacetime ≃ₗᵢ[ℝ] Spacetime)
      (R : Ward.Rotation), (∀ a, sign a = 1 ∨ sign a = -1) →
      (∀ a, U (EuclideanSpace.single a 1) = sign a • EuclideanSpace.single (σ a) 1) →
      (∀ x, Matrix.toEuclideanLin R.val x = U x) → ∀ v w : B.sector d,
      RelatedByAxes B σ sign U v.val w.val → W.act d R (frame r d v) = frame r d w
  unit (d : ℕ) (v : B.sector d) (unitField : v.val = 1) : ∀ᶠ r : ℝ in 𝓝[>] 0,
    ∀ (phase : Option T.Character) (n : ℕ) (fields : Fin n → T.Tag) (x : Points (n+1)),
      x ∈ WilsonFamily.separated _ →
        T.correlation phase (Fin.cons ⟨d, frame r d v⟩ fields) x =
        T.correlation phase fields (WithLp.toLp 2 fun i => x.ofLp i.succ)
  includeField {d e : ℕ} : d ≤ e → T.Field d →ₗ[ℂ] T.Field e
  includeLabel {d e : ℕ} (h : d ≤ e) (v : T.Field d) :
    T.toLabel e (includeField h v) = T.toLabel d v
  includeInsertion {d e : ℕ} (h : d ≤ e) (v : T.Field d) (phase : Option T.Character)
      (n : ℕ) (fields : Fin n → T.Tag) (x : Points (n+1)) (hx : x ∈ WilsonFamily.separated _) :
    T.correlation phase (Fin.cons ⟨e, includeField h v⟩ fields) x =
      T.correlation phase (Fin.cons ⟨d, v⟩ fields) x
  multilinear (phase : Option T.Character) (n : ℕ) (d : Fin n → ℕ)
      (x : Points n) (hx : x ∈ WilsonFamily.separated n) :
    ∃ L : MultilinearMap ℂ (fun i => T.Field (d i)) ℂ, ∀ v,
      T.correlation phase (fun i => ⟨d i, v i⟩) x = L v

variable {B : Maxwell.Reference g} {T : Hierarchy C}

def Measurement.inputs (H : Measurement B T) {n : ℕ}
    (r : ℝ) (fields : Fin n → Label B) : Fin n → T.Tag :=
  fun i => ⟨(fields i).1, H.frame r (fields i).1 (fields i).2⟩

/-- The running coupling is read from a signed three-point measurement in
position space. The same normalized frame realizes the numerical field change. -/
def MeasuredNormalization (prescription : PositionPrescription B)
    {N : (d k : ℕ) → Module.End ℂ (B.sector d)}
    (adjustment : NumericalAdjustment B N) (H : Measurement B T) : Prop :=
  ∃ J : PositionFrames T B,
    PositionNormalized T prescription J ∧ PositionLocallyUnique T prescription J ∧
    PositionUnital T J ∧ PositionNested T J ∧ PositionReal T J ∧
    (∀ r : ℝ, 0 < r →
      let moment := positionMoment T J r 6 (n := 3)
      Integrable (fun x => prescription.triangle.profile x * prescription.triangle.connected moment x)) ∧
    (∀ r : ℝ, H.coupling r =
      prescription.triangle.measure (positionMoment T J r 6 (n := 3)) / prescription.triangle.cT) ∧
    ∀ d, ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ v, H.frame r d v = J r d (adjustment.value d (H.coupling r) v)

end YangMills.CorrelationMatching
