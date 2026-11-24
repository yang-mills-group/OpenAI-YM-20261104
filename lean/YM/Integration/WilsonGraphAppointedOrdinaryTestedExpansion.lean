import YangMills.WilsonProof.NativeSupport.CommissionedPublic.AppointedRoundedReader
import YangMills.WilsonProof.NativeSupport.CommissionedPublic.AppointedMeasuredJetMass
import YM.Integration.WilsonGraphCenteredFarFiledBook
import YM.Integration.WilsonGraphSeparatedRegularity
import YM.FVA2.Gen.Flat
import YM.Integration.WilsonGraphCenteredFarReplacement
import YM.GradedFar.Physical.Contours
import YM.GradedFar.Elected.Voters
import YM.GradedFar.FormalDemand
import YM.XSpace.Playing
import YM.XSpace.Cart
import YM.XSpace.Tamarack
import YM.XSpace.Pivots
import YM.UVNext.FREE_STRESS_CERTIFICATE.Size
import YM.OPE.Schemes.Rearrange
import YM.OPE.Splitting.Detector
import YM.OPE.Short.Gap
import YM.Integration.WilsonGraphCenteredFarPhysicalMass
import YM.Integration.WilsonGraphCenteredFarHeaterRate
import YM.GradedFar.Demand
import YangMills.WilsonProof.NativeSupport.CommissionedPublic.AppointedRaisedReceives
import YM.GradedFar.Crop
import YM.OPE.Splitting.Observe
import YM.GradedFar.Continuation.Insert
import YM.GradedFar.Round.Geometry
import YM.Integration.WilsonGraphCenteredRoundedSource
import YM.GradedFar.Round.G9
import YM.Integration.WilsonGraphAppointedOrdinaryWordMass
import YangMills.WilsonProof.NativeSupport.CommissionedPublic.AppointedAllFieldCharts
import YangMills.WilsonProof.NativeSupport.CommissionedPublic.AppointedFullOrdinaryJet
import YangMills.WilsonProof.NativeSupport.CommissionedPublic.AppointedDerivativeBook
import YangMills.WilsonProof.NativeSupport.CommissionedPublic.AppointedDerivativeFrames
import YangMills.WilsonProof.NativeSupport.CommissionedPublic.AppointedCartesianWords
import YM.Integration.WilsonGraphAppointedRaisedOrdinaryPurchases
import YM.Integration.WilsonGraphUniformMixedShapeMass
import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7StandaloneMeasuredCorrelationEstimates

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace YM.Integration.GradedFar.AppointedOrdinaryPurchases

open Filter Set _root_.YangMills _root_.YangMills.Matching Answer.ContinuumLimit
open scoped Topology Classical BigOperators

universe u
variable (g : GaugeGroup) (hg : g.IsSimple) (periods : ℕ → ℕ) (mono : StrictMono periods)
private abbrev elected := WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order periods mono)
private abbrev reader := AppointedOrdinaryPacket.measurement hg (elected.{u} g hg periods mono)
  (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) (WilsonGraphPaperPublication.perspective.{u} g hg)
private abbrev conversion := AppointedGraphOrdinaryConversion.filedConversion g hg

private theorem scaleValue {n : ℕ} {f a : _root_.YangMills.Points n → ℂ} {x : _root_.YangMills.Points n} {D : ℝ}
    (price : shapeJetEstimateAt 0 f a x D) (z : ℂ) :
    shapeJetEstimateAt 0 (fun y => z * f y) (fun y => z * a y) x (‖z‖ * D) := by
  refine ⟨contDiffAt_const.mul price.1,contDiffAt_const.mul price.2.1,?_⟩
  intro j hj
  have zero : j = 0 := Nat.eq_zero_of_le_zero hj
  subst j
  simp only [norm_iteratedFDeriv_zero,←mul_sub,norm_mul]
  exact mul_le_mul_of_nonneg_left (CorrelationOnly.shapeValue price) (norm_nonneg z)

/-- Every output covector has the public signed-test expansion, with both integrability conclusions. -/
theorem tested {n h : ℕ} (income : AtOutput.{u} g hg periods mono n h)
    (d : Fin n → ℕ) (v : (i : Fin n) → (maxwellReference g).sector (d i))
    (o : Spacetime) (out : (maxwellReference g).sector h →ₗ[ℂ] ℂ) :
    let H := reader.{u} g hg periods mono
    let a : Fin n → Label (maxwellReference g) := fun i => ⟨d i,v i⟩
    HasExpansion 0 H.clock (fun r x => out (H.wilsonOPE r h a o x))
      (fun k x => out ((conversion g hg).ope (_root_.IssuedMaxwell.GraphCoefficients.issued g) h k a x)) := by
  classical
  let H := reader.{u} g hg periods mono
  let a : Fin n → Label (maxwellReference g) := fun i => ⟨d i,v i⟩
  obtain ⟨C,hC,bounded⟩ := WilsonGraphUniformMixedShapeMass.dualBound
    ((maxwellReference g).sector h) (MS.Theater.Daylight (FVA2.Press.portDeck g.core) h) out
  let b : ℝ := C+1
  have hb : 0 < b := by dsimp [b]; linarith
  let small : (maxwellReference g).sector h →ₗ[ℂ] ℂ := ((b : ℂ)⁻¹) • out
  have contractive (w : (maxwellReference g).sector h) : ‖small w‖ ≤ sectorMass w := by
    have step : ‖out w‖ ≤ C * sectorMass w := bounded w
    change ‖(b : ℂ)⁻¹ * out w‖ ≤ sectorMass w
    rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hb,←div_eq_inv_mul]
    apply (div_le_iff₀ hb).2
    dsimp [b]
    nlinarith [sectorMass_nonneg w]
  have restore (w : (maxwellReference g).sector h) : (b : ℂ) * small w = out w := by
    change (b : ℂ) * ((b : ℂ)⁻¹ * out w) = out w
    rw [←mul_assoc,mul_inv_cancel₀ (by exact_mod_cast (ne_of_gt hb)),one_mul]
  apply CorrelationOnly.testedOfShapeJets H.positive
    (CorrelationOnly.clockAtZero (CorrelationOnly.Measurement.ofOriginal H))
  intro p K compact separated
  obtain ⟨A,hA,late⟩ := income p 0 d K compact separated
  refine ⟨b * (A * ∏ i, sectorMass (v i)),
    mul_nonneg hb.le (mul_nonneg hA (Finset.prod_nonneg fun i _ => sectorMass_nonneg (v i))),?_⟩
  filter_upwards [late] with r paid
  intro x hx
  have scaled := scaleValue (paid v o x hx small contractive) (b : ℂ)
  simp only [restore,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hb,mul_assoc] at scaled
  change shapeJetEstimateAt 0 (fun y => out (H.wilsonOPE r h a o y))
    (fun y => ∑ k : Fin (p+1), (H.clock r : ℂ)^k.val *
      out ((conversion g hg).ope (_root_.IssuedMaxwell.GraphCoefficients.issued g) h k.val a y))
    x ((b * (A * ∏ i, sectorMass (v i))) * |H.clock r|^(p+1))
  simpa only [map_sum,map_smul,smul_eq_mul,mul_assoc] using scaled

end YM.Integration.GradedFar.AppointedOrdinaryPurchases
end

