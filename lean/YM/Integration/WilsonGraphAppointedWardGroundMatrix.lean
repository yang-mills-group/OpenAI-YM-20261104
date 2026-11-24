import YM.Integration.WilsonGraphWardGroundMatrix
import YM.Integration.WilsonGraphSeparatedFiledEstimates
import YM.Integration.WilsonGraphGroupPositionReference
import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7StandaloneFiledWardMatrixCoefficients
import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7StandaloneSmearedWardMatrixExpansion

/-! The independent four-row matrix at its appointed formal entries. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonGraphAppointedWardGroundMatrix
open _root_.YangMills _root_.YangMills.Matching _root_.YangMills.Matching.WardStress
open _root_.PhysicalMatching.H7StandaloneFourSmearedWardReadings (Pupils probes)
open _root_.PhysicalMatching.H7StandaloneAppointedPublicWardRows (columns)
open _root_.PhysicalMatching.H7StandaloneFiledWardMatrixCoefficients (groupMarked matrixCoefficients)
open WilsonGraphWardGroundMatrix (reading matrix Tested zeroReading)
open MeasureTheory
open scoped BigOperators Classical
variable {g : GaugeGroup}
local notation "B₀" => maxwellReference g
local notation "M₀" => _root_.IssuedMaxwell.GraphCoefficients.issued g

theorem converted (S : Conversion B₀) {n : ℕ} (k : ℕ) (v : Fin n → _root_.YangMills.Matching.Label B₀)
    (x : Points n) (hx : x ∈ separated n) :
    WilsonGraphStandaloneCorrelation.converted S k v x = S.correlation M₀ k v x := by
  let N := { M₀ with correlation := WilsonGraphStandaloneCorrelation.bare g }
  exact ((CorrelationOnly.filedConvertedAt (M := M₀) (N := N)
    (fun {j} q a z hz => WilsonGraphGroupPositionReference.agreement g j q a z hz) S k v x hx).trans
      (WilsonGraphStandaloneCorrelation.converted_read S N rfl k v x)).symm

variable {H : g.core.Simple} (Z : _root_.YM.FVA2.Register.WilsonPrescription g.core)
  (Q : _root_.YM.Answer.ContinuumLimit.Perspective H Z true)

local notation "S₀" => _root_.IssuedBridge.PostedAppointedConversion.filed
  Z Q.MS Q.matching (_root_.YM.FVA2.Teller.logNu 1)

theorem marked {n : ℕ} (a : Axis) (m : Fin 4) (t : Fin n → Fin 2)
    (x : Points (n+1)) (hx : x ∈ separated (n+1)) :
    groupMarked Z Q 0 a 0 m t x =
      reading S₀ (fun i => probes H (t i)) (columns H a 0 m) x := by
  calc
    _ = (S₀).correlation M₀ 0 _ x := converted S₀ 0 _ x hx
    _ = _ := by
      unfold reading
      apply congrArg (fun f => (S₀).correlation M₀ 0 f x)
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> rfl

private theorem basisPoint {n : ℕ} (a : Axis) (m : Fin 4) (t : Fin n → Fin 2)
    (q : Fin n → _root_.YangMills.Matching.Label (_root_.IssuedMaxwell.Reports.B g))
    (hq : q = fun i => ⟨4, probes H (t i)⟩)
    (x : Points (n+1)) (hx : x ∈ separated (n+1)) :
    GroundDifference.ground M₀ S₀ (columns H a 0 m) 0 q x =
      groupMarked Z Q 0 a 0 m t x := by
  subst q
  change reading S₀ _ _ x - reading S₀ (fun i => probes H (t i)) 0 x = _
  rw [zeroReading S₀ _ _ hx, sub_zero, marked Z Q a m t x hx]

private theorem basisTest {n : ℕ} (a : Axis) (m : Fin 4) (t : Fin n → Fin 2)
    {X : Type*} [MeasureSpace X] (shape : X → Points (n+1)) (weight : X → ℂ)
    (occupied : ∀ z, weight z ≠ 0 → shape z ∈ separated (n+1)) :
    (∫ z, weight z * GroundDifference.ground M₀ S₀ (columns H a 0 m) 0
      (fun i => ⟨4, probes H (t i)⟩) (shape z)) =
      ∫ z, weight z * groupMarked Z Q 0 a 0 m t (shape z) := by
  apply integral_congr_ae
  filter_upwards [] with z
  by_cases h : weight z = 0
  · simp [h]
  · exact congrArg (fun c : ℂ => weight z * c)
      (basisPoint Z Q a m t _ rfl (shape z) (occupied z h))

set_option maxHeartbeats 1600000 in
theorem atPupils (P : Pupils) : matrix S₀ H P = matrixCoefficients Z Q P 0 := by
  funext i m
  have vacuum : (∫ x : Points 1, P.vacuum x * GroundDifference.ground M₀ S₀
        (columns H 0 0 m) 0 (fun j : Fin 0 => Fin.elim0 j) x) =
      _root_.PhysicalMatching.H7StandaloneFiledWardMatrixCoefficients.vacuumEntry Z Q P 0 m := by
    unfold _root_.PhysicalMatching.H7StandaloneFiledWardMatrixCoefficients.vacuumEntry
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases h : P.vacuum x = 0
    · simp [h]
    · exact congrArg (fun c : ℂ => P.vacuum x * c)
        (basisPoint Z Q (n := 0) 0 m (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
          (funext (fun i => Fin.elim0 i)) x
          (P.vacuum.tsupport_subset (subset_tsupport _ h)))
  have conservation (row : Fin 2) :
      (∑ j : Fin 2, ∑ a : Axis, ∫ x : Points 2,
        Ward.firstDerivative a (fun y => P.conservation row j y) x *
          GroundDifference.ground M₀ S₀ (columns H a 0 m) 0
            (fun _ : Fin 1 => ⟨4, probes H j⟩) x) =
      _root_.PhysicalMatching.H7StandaloneFiledWardMatrixCoefficients.conservationEntry Z Q P 0 row m := by
    unfold _root_.PhysicalMatching.H7StandaloneFiledWardMatrixCoefficients.conservationEntry
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro a _
    simpa only [id_eq] using basisTest Z Q a m (fun _ : Fin 1 => j) (X := Points 2) id
      (Ward.firstDerivative a (fun y => P.conservation row j y))
      (fun x hx => (_root_.PhysicalMatching.H7StandaloneSmearedWardMatrixExpansion.derivativeWeight
        (P.conservation row j) a).2.2 (subset_tsupport _ hx))
  have flux : -(∑ a : Axis, ∫ z : Spacetime × Points 2,
      _root_.PhysicalMatching.H7StandaloneTranslationTestSupport.weight P a z *
        GroundDifference.ground M₀ S₀ (columns H a 0 m) 0
          (fun _ : Fin 2 => ⟨4, probes H 0⟩) (Ward.prepend z.1 z.2)) =
      _root_.PhysicalMatching.H7StandaloneFiledWardMatrixCoefficients.fluxEntry Z Q P 0 m := by
    unfold _root_.PhysicalMatching.H7StandaloneFiledWardMatrixCoefficients.fluxEntry
    apply congrArg Neg.neg
    apply Finset.sum_congr rfl
    intro a _
    exact basisTest Z Q a m (fun _ : Fin 2 => 0)
      (fun z : Spacetime × Points 2 => Ward.prepend z.1 z.2)
      (_root_.PhysicalMatching.H7StandaloneTranslationTestSupport.weight P a)
      (fun z hz => _root_.PhysicalMatching.H7StandaloneTranslationTestSupport.separated P a
        (subset_tsupport _ hz))
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases hi with rfl | rfl | rfl | rfl
  · simp only [matrix, WilsonGraphWardFourGroundTests.rows, matrixCoefficients,
      Matrix.cons_val_zero]
    exact vacuum
  · rw [show (1 : Fin 4) = Fin.succ ((0 : Fin 3)) by rfl]
    simp only [matrix, WilsonGraphWardFourGroundTests.rows, matrixCoefficients,
      Matrix.cons_val_succ, Matrix.cons_val_zero]
    exact conservation 0
  · rw [show (2 : Fin 4) = Fin.succ (Fin.succ ((0 : Fin 2))) by rfl]
    simp only [matrix, WilsonGraphWardFourGroundTests.rows, matrixCoefficients,
      Matrix.cons_val_succ, Matrix.cons_val_zero]
    exact conservation 1
  · rw [show (3 : Fin 4) = Fin.succ (Fin.succ (Fin.succ ((0 : Fin 1)))) by rfl]
    simp only [matrix, WilsonGraphWardFourGroundTests.rows, matrixCoefficients,
      Matrix.cons_val_succ, Matrix.cons_val_zero]
    exact flux

end YM.Integration.WilsonGraphAppointedWardGroundMatrix
