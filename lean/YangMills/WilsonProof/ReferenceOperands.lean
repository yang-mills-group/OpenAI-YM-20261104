import YangMills.WilsonProof.NativeGraph

set_option autoImplicit false
noncomputable section
namespace YangMills.WilsonProof
open PerturbativeMatching MSbar Matching
variable {g : GaugeGroup} {B : Maxwell.Reference g} {M N : MSbar.Coefficients B}

private theorem momentsOnSameCorrelations (same : M.correlation = N.correlation) :
    Position.momentThrough M = Position.momentThrough N := by
  unfold Position.momentThrough
  rw [same]

private theorem prefixOnSameCorrelations (same : M.correlation = N.correlation)
    (P : PositionPrescription B) : Position.framePrefix M P = Position.framePrefix N P := by
  have report : Position.residualReport M = Position.residualReport N := by
    unfold Position.residualReport
    rw [momentsOnSameCorrelations same]
  funext d k
  induction k with
  | zero => rfl
  | succ k ih => simp only [Position.framePrefix, ih, report]

theorem rawOnSameCorrelations (same : M.correlation = N.correlation) (P : PositionPrescription B)
    (law : Position.RawValid M P) : Position.RawValid N P := by
  have moment := momentsOnSameCorrelations same
  have framePrefixEq := prefixOnSameCorrelations same P
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [same] using law.tree
  · simpa only [Position.rawFrame, framePrefixEq] using law.nested
  · simpa only [moment, framePrefixEq] using law.residualIntegrable
  · simpa only [Position.rawMoment, moment, framePrefixEq] using law.integrable
  · have report : Position.rawReport M P = Position.rawReport N P := by
      unfold Position.rawReport Position.rawMoment
      rw [moment, framePrefixEq]
    intro d k
    rw [← report]
    exact law.normalized d k

theorem validOnSameCorrelations (same : M.correlation = N.correlation)
    (P : PositionPrescription B) (S : PositionConversion B) (law : ConversionValid M P S) :
    ConversionValid N P S := by
  have framePrefixEq := prefixOnSameCorrelations same P
  have frame : Position.rawFrame M P = Position.rawFrame N P := by
    unfold Position.rawFrame
    rw [framePrefixEq]
  have moment : Position.rawMoment M P = Position.rawMoment N P := by
    unfold Position.rawMoment
    rw [momentsOnSameCorrelations same, framePrefixEq]
  have kernel : Position.triangleKernel M P = Position.triangleKernel N P := by
    unfold Position.triangleKernel
    rw [moment]
  have amplitude : Position.triangleAmplitude M P = Position.triangleAmplitude N P := by
    unfold Position.triangleAmplitude
    rw [kernel]
  have measured : Position.measuredCoupling M P = Position.measuredCoupling N P := by
    unfold Position.measuredCoupling
    rw [amplitude]
  have reading : Position.positionReading M P = Position.positionReading N P := by
    unfold Position.positionReading
    rw [measured]
  have coupling : Position.msCoupling M P = Position.msCoupling N P := by
    unfold Position.msCoupling
    rw [reading]
  have field : Position.reparametrizedFrame M P = Position.reparametrizedFrame N P := by
    unfold Position.reparametrizedFrame
    rw [coupling, frame]
  have raw := rawOnSameCorrelations same P law.raw
  have slope : P.triangle.RawSlopeAgrees N := by
    simpa only [Position.Triangle.RawSlopeAgrees, Position.Triangle.firstConnected, same] using law.rawSlope
  cases law
  constructor <;> try simp only [← kernel, ← amplitude, ← measured, ← reading, ← coupling, ← field]
  all_goals assumption

theorem calibrationOnSameCorrelations {A A' : MSbar.Coefficients (maxwellReference g)}
    (same : A.correlation = A'.correlation) (S : PositionScheme g) (law : Calibration A S) :
    Calibration A' S := by
  have valid := validOnSameCorrelations same S.prescription S.series law.conversionValid
  obtain ⟨m, o⟩ := A
  obtain ⟨n, q⟩ := A'
  change m = n at same
  subst n
  exact ⟨law.admissible, law.signedSlope, valid, law.adjustmentValue⟩

theorem wardOnSameCorrelations (same : M.correlation = N.correlation)
    (S : Conversion B) (P : WardStress.Series B) (law : WardStress.Determined M S P) :
    WardStress.Determined N S P := by
  obtain ⟨m, o⟩ := M
  obtain ⟨n, q⟩ := N
  change m = n at same
  subst n
  cases law
  constructor <;> assumption

theorem convertedOPEOnSameArray (same : M.ope = N.ope) (S : Conversion B) {n : ℕ}
    (h k : ℕ) (fields : Fin n → Label B) (x : Points n) :
    S.ope M h k fields x = S.ope N h k fields x := by
  obtain ⟨c, o⟩ := M
  obtain ⟨c', o'⟩ := N
  change o = o' at same
  subst o'
  rfl

end YangMills.WilsonProof
