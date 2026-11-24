import YangMills.WilsonProof.NativeSupport.MeasuredShapeJets
import YangMills.WilsonProof.NativeSupport.PhaseProximity
import YangMills.WilsonProof.NativeSupport.MSPhysicalAppointment
import MSConversion
import YangMills.WilsonProof.NativeSupport.MSFormalSeries
import MSPositionFrame
import MSPositionPrescription
import MSPositionScreens
import FormalConversion
import MSReference
import YangMills.WilsonProof.NativeSupport.YangMills.FreeFields
import YangMills.WilsonProof.NativeSupport.MSPositionLabels
import MSScalarReverse
import MSScalarInverse
import YangMills.WilsonProof.NativeSupport.WilsonConstruction
import YangMills.WilsonProof.NativeSupport.WardStressSeries
import YangMills.WilsonProof.NativeSupport.FrameNormalization

set_option autoImplicit false

noncomputable section

namespace YangMills.Matching.CorrelationOnly

open Filter Set MeasureTheory
open scoped Topology BigOperators Classical ContDiff

variable {g : GaugeGroup} {B : Maxwell.Reference g}
variable {C : WilsonFamily g} {T : Hierarchy C}

structure Measurement (B : Maxwell.Reference g) (T : Hierarchy C) where
  clock : ℝ → ℝ
  positive : ∀ᶠ s : ℝ in 𝓝[>] 0, 0 < clock s
  oneLoop : Tendsto (fun s => clock s * Real.sqrt (2 * oneLoopBeta B * Real.log s⁻¹))
    (𝓝[>] 0) (𝓝 1)
  frame (s : ℝ) (d : ℕ) : B.sector d ≃ₗ[ℂ] T.Field d
  nested (d e : ℕ) (p : B.sector d) (q : B.sector e) (eq : p.val = q.val) :
    ∀ᶠ s : ℝ in 𝓝[>] 0, T.toLabel d (frame s d p) = T.toLabel e (frame s e q)
  /-- One physical Ward action implements the signed-axis action on the reported
  fields at every sufficiently small length, on each finite filtration. -/
  frameAxes : ∃ W : T.StressWardLaws, ∀ d, ∀ᶠ s : ℝ in 𝓝[>] 0,
    ∀ (σ : Equiv.Perm Axis) (sign : Axis → ℝ) (U : Spacetime ≃ₗᵢ[ℝ] Spacetime)
      (R : Ward.Rotation), (∀ a, sign a = 1 ∨ sign a = -1) →
      (∀ a, U (EuclideanSpace.single a 1) = sign a • EuclideanSpace.single (σ a) 1) →
      (∀ x, Matrix.toEuclideanLin R.val x = U x) → ∀ p q : B.sector d,
      RelatedByAxes B σ sign U p.val q.val → W.act d R (frame s d p) = frame s d q
  unit (d : ℕ) (p : B.sector d) (hp : p.val = 1) : ∀ᶠ s : ℝ in 𝓝[>] 0,
    ∀ (phase : Option T.Character) (n : ℕ) (a : Fin n → T.Tag) (x : Points (n+1)),
      x ∈ WilsonFamily.separated _ →
        T.correlation phase (Fin.cons ⟨d,frame s d p⟩ a) x =
        T.correlation phase a (WithLp.toLp 2 (fun i => x.ofLp i.succ))
  includeField {j h : ℕ} : j ≤ h → T.Field j →ₗ[ℂ] T.Field h
  includeLabel {j h : ℕ} (hj : j ≤ h) (v : T.Field j) :
    T.toLabel h (includeField hj v) = T.toLabel j v
  includeInsertion {j h : ℕ} (hj : j ≤ h) (v : T.Field j) (phase : Option T.Character)
      (n : ℕ) (a : Fin n → T.Tag) (x : Points (n+1)) (hx : x ∈ WilsonFamily.separated _) :
    T.correlation phase (Fin.cons ⟨h,includeField hj v⟩ a) x =
      T.correlation phase (Fin.cons ⟨j,v⟩ a) x
  multilinear (phase : Option T.Character) (n : ℕ) (d : Fin n → ℕ)
      (x : Points n) (hx : x ∈ WilsonFamily.separated n) :
    ∃ moment : MultilinearMap ℂ (fun i => T.Field (d i)) ℂ, ∀ v,
      T.correlation phase (fun i => ⟨d i,v i⟩) x = moment v

namespace Measurement
variable (H : Measurement B T)

def inputs {n : ℕ} (s : ℝ) (a : Fin n → Label B) : Fin n → T.Tag :=
  fun i => ⟨(a i).1, H.frame s (a i).1 (a i).2⟩


/-- Project a full measurement to its measured correlation fields. -/
def ofOriginal (A : Matching.Measurement B T) : Measurement B T where
  clock := A.clock
  positive := A.positive
  oneLoop := A.oneLoop
  frame := A.frame
  nested := A.nested
  frameAxes := A.frameAxes
  unit := A.unit
  includeField := A.includeField
  includeLabel := A.includeLabel
  includeInsertion := A.includeInsertion
  multilinear := A.multilinear

end Measurement

def correlationError (M : MSbar.Coefficients B) (S : Conversion B) (H : Measurement B T)
    {n : ℕ} (p : ℕ) (a : Fin n → Label B) (phase : Option T.Character)
    (o : Spacetime) (s : ℝ) (x : Points n) : ℂ :=
  T.correlation phase (H.inputs s a) (WithLp.toLp 2 fun i => o + s • x i) -
    ∑ k : Fin (p+1), (H.clock s : ℂ)^k.val * S.correlation M k.val a x

end YangMills.Matching.CorrelationOnly

namespace YangMills.Matching.CorrelationOnly
open Filter Set MeasureTheory
open scoped Topology BigOperators Classical ContDiff
variable {g : GaugeGroup} {B : Maxwell.Reference g}
variable {C : WilsonFamily g} {T : Hierarchy C}

def phaseDifference (H : Measurement B T) {n : ℕ} (s : ℝ) (o : Spacetime)
    (a : Fin n → Label B) (p q : Option T.Character) (x : Points n) : ℂ :=
  let position : Points n := WithLp.toLp 2 fun i => o + s • x i
  T.correlation p (H.inputs s a) position - T.correlation q (H.inputs s a) position

/-- The same radius event controls every character, the Wilson mean, all
centers, all input fields and the indicated spatial derivatives. The returned
hierarchy, the finite input caps, the compact and the exponent are fixed first. -/
def PhaseProximity (H : Measurement B T) : Prop :=
  ∀ (n j : ℕ) (d : Fin n → ℕ) (K : Set (Points n)),
    IsCompact K → K ⊆ WilsonFamily.separated n →
    ∀ γ : ℝ, 0 < γ → γ < 4 → ∀ᶠ s : ℝ in 𝓝[>] 0,
    ∀ (p q : Option T.Character) (o : Spacetime)
        (v : (i : Fin n) → B.sector (d i)) (x : Points n), x ∈ K →
      ‖iteratedFDeriv ℝ j (phaseDifference H s o (fun i => ⟨d i, v i⟩) p q) x‖ ≤
        s ^ γ * ∏ i, sectorMass (v i)

def namedStress (H : Measurement B T) (P : WardStress.Series B) : Prop :=
  ∀ (a b : Axis) (N : ℕ) (out : B.sector 4 →ₗ[ℂ] ℂ),
    Tendsto (fun s : ℝ =>
      (out ((H.frame s 4).symm ((s : ℂ)^4 • T.stress a b)) -
        ∑ j : Fin (N+1), (H.clock s : ℂ)^j.val * out (P j.val a b)) /
          (H.clock s : ℂ)^N) (𝓝[>] 0) (𝓝 0)

/-- All correlation estimates on the appointed measurement. -/
structure Estimates (M : MSbar.Coefficients B) (S : Conversion B) (H : Measurement B T) : Prop where
  tested (n : ℕ) (d : Fin n → ℕ) : ∃ m : ℕ,
    ∀ (phase : Option T.Character) (v : (i : Fin n) → B.sector (d i)) (o : Spacetime),
      let a : Fin n → Label B := fun i => ⟨d i, v i⟩
      HasExpansion m H.clock (fun s x => T.correlation phase (H.inputs s a)
        (WithLp.toLp 2 fun i => o + s • x i)) (fun k x => S.correlation M k a x)
  compact (n p : ℕ) (d : Fin n → ℕ) (o : Spacetime) (K : Set (Points n))
      (compact : IsCompact K) (separated : K ⊆ WilsonFamily.separated n) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ phase : Option T.Character,
      ∀ (v : (i : Fin n) → B.sector (d i)) (x : Points n), x ∈ K →
      ‖correlationError M S H p (fun i => ⟨d i, v i⟩) phase o s x‖ ≤
        A * (∏ i, sectorMass (v i)) * |H.clock s|^(p+1)
  jets (n p j : ℕ) (d : Fin n → ℕ) (K : Set (Points n))
      (compact : IsCompact K) (separated : K ⊆ WilsonFamily.separated n) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ (phase : Option T.Character)
      (v : (i : Fin n) → B.sector (d i)) (o : Spacetime) (x : Points n), x ∈ K →
      let a : Fin n → Label B := fun i => ⟨d i, v i⟩
      shapeJetEstimateAt j
        (fun y => T.correlation phase (H.inputs s a) (WithLp.toLp 2 fun i => o + s • y i))
        (fun y => ∑ k : Fin (p+1), (H.clock s : ℂ)^k.val * S.correlation M k.val a y)
        x (A * (∏ i, sectorMass (v i)) * |H.clock s|^(p+1))
  phases : PhaseProximity H
  wardIndependent : ∃! P : WardStress.Series B, WardStress.Determined M S P
  wardNamed : ∀ P : WardStress.Series B, WardStress.Determined M S P → namedStress H P

end YangMills.Matching.CorrelationOnly

namespace YangMills.MSbar.CorrelationOnly
open Filter MeasureTheory
open scoped Topology BigOperators Classical
variable {g : GaugeGroup} {B : Maxwell.Reference g}

def appointed (P : PositionPrescription B) {N : (d k : ℕ) → Module.End ℂ (B.sector d)}
    (L : NumericalAdjustment B N) (C : WilsonFamily g) (T : Hierarchy C)
    (H : Matching.CorrelationOnly.Measurement B T) : Prop :=
  ∃ J : PositionFrames T B,
    PositionNormalized T P J ∧ PositionLocallyUnique T P J ∧
    PositionUnital T J ∧ PositionNested T J ∧ PositionReal T J ∧
    (∀ᶠ s : ℝ in 𝓝[>] 0,
      let m := positionMoment T J s 6 (n := 3)
      Integrable (fun x => P.triangle.profile x * P.triangle.connected m x) ∧
      H.clock s = P.triangle.measure m / P.triangle.cT) ∧
    ∀ d, ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ v, H.frame s d v = J s d (L.value d (H.clock s) v)


theorem appointed_ofOriginal {P : PositionPrescription B}
    {N : (d k : ℕ) → Module.End ℂ (B.sector d)} {L : NumericalAdjustment B N}
    {C : WilsonFamily g} {T : Hierarchy C} {H : Matching.Measurement B T}
    (h : MSbar.appointed P L C T H) :
    appointed P L C T (Matching.CorrelationOnly.Measurement.ofOriginal H) := h

end YangMills.MSbar.CorrelationOnly
