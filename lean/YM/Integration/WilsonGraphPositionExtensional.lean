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
import YM.Integration.WilsonGraphStandaloneCorrelation

set_option autoImplicit false
noncomputable section

namespace YM.Integration.WilsonGraphPositionExtensional
open YangMills YangMills.MSbar YangMills.MSbar.Position
open MeasureTheory Function Set
open scoped Classical BigOperators

variable {g : YangMills.GaugeGroup} {B : YangMills.Maxwell.Reference g}
  {M N : YangMills.MSbar.Coefficients B}

def SeparatedRead (M N : YangMills.MSbar.Coefficients B) : Prop :=
  ∀ (n k : ℕ) (a : Fin n → YangMills.Matching.Label B) (x : YangMills.Points n),
    x ∈ YangMills.separated n → M.correlation n k a x = N.correlation n k a x

private theorem tested {n : ℕ} (φ : YangMills.SeparatedTest n)
    {f h : YangMills.Points n → ℂ}
    (same : ∀ x ∈ YangMills.separated n, f x = h x) :
    (fun x => φ x * f x) = (fun x => φ x * h x) := by
  funext x
  by_cases hx : x ∈ YangMills.separated n
  · rw [same x hx]
  · have zero : φ x = 0 := notMem_support.mp (fun h => hx (φ.tsupport_subset (subset_closure h)))
    simp only [zero, zero_mul]

theorem through (read : SeparatedRead M N) (d k r : ℕ) (A : Fin (r+1) → EndAt B d)
    (n : ℕ) (v : Fin n → B.sector d) (x : YangMills.Points n) (hx : x ∈ YangMills.separated n) :
    momentThrough M d k r A n v x = momentThrough N d k r A n v x := by
  unfold momentThrough
  apply Finset.sum_congr rfl
  intro ν _
  by_cases keep : (∑ i, (ν i).val) ≤ k
  · simpa only [if_pos keep] using read n (k - ∑ i, (ν i).val)
      (fun i => ⟨d, A (ν i) (v i)⟩) x hx
  · simp only [if_neg keep]

private theorem residual (read : SeparatedRead M N) (d k : ℕ) (A : Fin (k+1) → EndAt B d) :
    residualReport M d k A = residualReport N d k A := by
  funext n φ v
  unfold residualReport
  rw [tested φ (fun x hx => through read d (k+1) k A n v x hx)]

theorem «prefix» (read : SeparatedRead M N) (P : PositionPrescription B) (d k : ℕ) :
    framePrefix M P d k = framePrefix N P d k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [framePrefix, ih, residual read]

theorem frame (read : SeparatedRead M N) (P : PositionPrescription B) :
    rawFrame M P = rawFrame N P := by
  funext d k
  unfold rawFrame
  rw [«prefix» read P d k]

theorem raw (read : SeparatedRead M N) (P : PositionPrescription B) (d k n : ℕ)
    (v : Fin n → B.sector d) (x : YangMills.Points n) (hx : x ∈ YangMills.separated n) :
    rawMoment M P d k n v x = rawMoment N P d k n v x := by
  unfold rawMoment
  rw [«prefix» read P d k]
  exact through read d k k _ n v x hx

private theorem reports (read : SeparatedRead M N) (P : PositionPrescription B) :
    rawReport M P = rawReport N P := by
  funext d k n φ v
  unfold rawReport
  rw [tested φ (fun x hx => raw read P d k n v x hx)]

theorem rawValid (read : SeparatedRead M N) (P : PositionPrescription B) (paid : RawValid M P) :
    RawValid N P where
  tree n d v x hx := (read n 0 _ x hx).symm.trans (paid.tree n d v x hx)
  nested d e k p q eq := by simpa only [frame read P] using paid.nested d e k p q eq
  residualIntegrable d k n φ v := by
    have original := paid.residualIntegrable d k n φ v
    rw [«prefix» read P d k] at original
    exact tested φ (fun x hx => through read d (k+1) k (framePrefix N P d k) n v x hx) ▸ original
  integrable d k n φ v := tested φ (fun x hx => raw read P d k n v x hx) ▸ paid.integrable d k n φ v
  normalized d k := by simpa only [reports read P] using paid.normalized d k

private theorem first (read : SeparatedRead M N) (t : Triangle B)
    (x : YangMills.Points 3) (hx : x ∈ YangMills.separated 3) :
    t.firstConnected M x = t.firstConnected N x := by
  have faces :
      (fun I : Finset (Fin 3) => PowerSeries.mk fun k => M.correlation 3 k (fun i => ⟨6,t.face I i⟩) x) =
        (fun I : Finset (Fin 3) => PowerSeries.mk fun k => N.correlation 3 k (fun i => ⟨6,t.face I i⟩) x) := by
    funext I
    exact congrArg PowerSeries.mk (funext fun k => read 3 k _ x hx)
  unfold Triangle.firstConnected
  rw [faces]

theorem slope (read : SeparatedRead M N) (t : Triangle B) :
    t.RawSlopeAgrees M ↔ t.RawSlopeAgrees N := by
  unfold Triangle.RawSlopeAgrees
  rw [tested t.profile (fun x hx => first read t x hx)]

private theorem kernel (read : SeparatedRead M N) (P : PositionPrescription B) (k : ℕ)
    (x : YangMills.Points 3) (hx : x ∈ YangMills.separated 3) :
    triangleKernel M P k x = triangleKernel N P k x := by
  have faces :
      (fun I : Finset (Fin 3) => PowerSeries.mk fun j => rawMoment M P 6 j 3 (P.triangle.face I) x) =
        (fun I : Finset (Fin 3) => PowerSeries.mk fun j => rawMoment N P 6 j 3 (P.triangle.face I) x) := by
    funext I
    exact congrArg PowerSeries.mk (funext fun j => raw read P 6 j 3 (P.triangle.face I) x hx)
  unfold triangleKernel
  rw [faces]

private theorem amplitudes (read : SeparatedRead M N) (P : PositionPrescription B) :
    triangleAmplitude M P = triangleAmplitude N P := by
  funext k
  unfold triangleAmplitude
  rw [tested P.triangle.profile (fun x hx => kernel read P k x hx)]

theorem valid (read : SeparatedRead M N) (P : PositionPrescription B) (W : PositionConversion B)
    (paid : ConversionValid M P W) : ConversionValid N P W := by
  have amp := amplitudes read P
  have measured : measuredCoupling M P = measuredCoupling N P := by
    funext k
    simp only [measuredCoupling, amp]
  have reading : positionReading M P = positionReading N P := by
    funext k
    simp only [positionReading, measured]
  have coupling : msCoupling M P = msCoupling N P := by simp only [msCoupling, reading]
  have fields : reparametrizedFrame M P = reparametrizedFrame N P := by
    simp only [reparametrizedFrame, coupling, frame read P]
  exact
    { raw := rawValid read P paid.raw
      integrable := fun k => tested P.triangle.profile (fun x hx => kernel read P k x hx) ▸ paid.integrable k
      freeOffset := by simpa only [amp] using paid.freeOffset
      rawSlope := (slope read P.triangle).mp paid.rawSlope
      signedTree := by simpa only [amp] using paid.signedTree
      nonzeroTree := paid.nonzeroTree
      real := fun k => by simpa only [reading, measured] using paid.real k
      slope := by simpa only [reading] using paid.slope
      coupling := paid.coupling.trans coupling
      inverseReading := fun k => by simpa only [reading] using paid.inverseReading k
      fields := by simpa only [fields] using paid.fields
      inverseFields := by simpa only [fields] using paid.inverseFields
      correction := by simpa only [fields] using paid.correction
      factorization := by simpa only [fields] using paid.factorization
      startsAtIdentity := paid.startsAtIdentity
      strictlyLowering := paid.strictlyLowering }

theorem forEveryBare (C : Coefficients (maxwellReference g))
    (selected : ∀ (n k : ℕ) (a : Fin n → YangMills.Matching.Label (maxwellReference g))
      (x : YangMills.Points n), x ∈ YangMills.separated n →
      C.correlation n k a x = WilsonGraphStandaloneCorrelation.bare g n k a x)
    (P : PositionPrescription (maxwellReference g)) (W : PositionConversion (maxwellReference g))
    (allSlopes : ∀ t : Triangle (maxwellReference g), t.Admissible → t.RawSlopeAgrees C)
    (paid : ConversionValid C P W)
    (M : Coefficients (maxwellReference g)) (reads : M.correlation = WilsonGraphStandaloneCorrelation.bare g) :
    (∀ t : Triangle (maxwellReference g), t.Admissible → t.RawSlopeAgrees M) ∧ ConversionValid M P W := by
  have read : SeparatedRead C M := by
    intro n k a x hx
    simpa only [reads] using selected n k a x hx
  exact ⟨fun t admissible => (slope read t).mp (allSlopes t admissible),valid read P W paid⟩

end YM.Integration.WilsonGraphPositionExtensional
end
