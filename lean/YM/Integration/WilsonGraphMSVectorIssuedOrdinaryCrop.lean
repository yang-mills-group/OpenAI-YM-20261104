import YM.GradedFar.Wave
import YM.Integration.WilsonGraphIssuedOrdinaryConversion
import YangMills.WilsonProof.NativeSupport.MeasuredShapeJets

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
noncomputable section
namespace YM.Integration.GradedFar.AppointedGraphMSVector
open PowerSeries YM.FVA2 YM.FVA2.Register YM.FVA2.Dframe YM.FVA2.O.Score
open YM.FVA2.O YM.FVA2.O.Enh YM.FVA2.O.Canon YM.FVA2.O.Project
open YM.FVA2.Scale YM.FVA2.GradedFar YM.XSpace YM.XSpace.Normalize YM.MS.Land
open YM.Integration _root_.IssuedMaxwell _root_.IssuedMaxwell.Reports
open scoped Classical BigOperators

universe u
variable (g : YangMills.GaugeGroup) (hg : g.IsSimple) {n : ℕ}
private abbrev N := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
private abbrev Z := WilsonCapturedPhysicalMSDatum.original g.core
private abbrev Qstar := WilsonGraphPaperPublication.perspective.{u} g hg
private abbrev S := (WilsonGraphGroupPositionReference.external g hg).conversion.conversion

/-- At the nominated reference the original far coefficient is the zero-aspect ordinary coefficient. -/
theorem series (d : Fin n → ℕ) (v : AppointedH140Inputs g.core d) (x : YM.Points n) (a : Q g.core) :
    msComponent (N g hg) (Z g) (Teller.logNu 1) v x a =
      AppointedGraphOrdinaryConversion.row.{u} g hg d v x a := by
  let N₀ := N g hg
  let Q₀ := Qstar.{u} g hg
  let ν := Teller.logNu 1
  have nominated : Q₀.MS = Z g := WilsonGraphPaperPublication.nominated.{u} g hg
  obtain ⟨ear, _, _, _⟩ := Q₀.matching.separatedOPE ν
  have same : (fun w : Scan g.core n => FarCoefficients (Equator.wave ν Q₀.MS) w x) =
      (fun w : Scan g.core n => OPECoefficients (Equator.wave ν Q₀.MS) w 0 x) :=
    funext fun w => (congrFun (ear.start_u w) x).symm
  change msComponent N₀ (Z g) ν v x a = _
  rw [← nominated]
  unfold msComponent msBills
  rw [same]
  rfl

/-- The entire original #140 vector, including every output coordinate, agrees with the public graph crop. -/
theorem publicCrop (d : Fin n → ℕ) (v : AppointedH140Inputs g.core d) (h p : ℕ) (x : YM.Points n) (t : ℝ) :
    msVector (N g hg) (Z g) (Teller.logNu 1) v x p h t =
      ∑ k : Fin (p+1), (t : ℂ)^k.val •
        (S g hg).ope (GraphCoefficients.issued g) h k.val (fun i => ⟨d i,v i⟩) x := by
  unfold msVector
  simp_rw [series.{0} g hg d v x, crop_eq]
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => (t : ℂ)^k •
    (S g hg).ope (GraphCoefficients.issued g) h k (fun i => ⟨d i,v i⟩) x)]
  exact AppointedGraphOrdinaryConversion.crop.{0} g hg d v h p x t

/-- The filed real derivative comparison uses the same public finite crop and the same dual. -/
theorem shapes (d : Fin n → ℕ) (v : AppointedH140Inputs g.core d) (h p j : ℕ) (t : ℝ)
    (actual : YM.Points n → ℂ) (out : Sec g.core h →ₗ[ℂ] ℂ) (x : YM.Points n) (fee : ℝ) :
    YangMills.Matching.shapeJetEstimateAt j actual
      (fun y => out (msVector (N g hg) (Z g) (Teller.logNu 1) v y p h t)) x fee ↔
    YangMills.Matching.shapeJetEstimateAt j actual (fun y => out (∑ k : Fin (p+1), (t : ℂ)^k.val •
      (S g hg).ope (GraphCoefficients.issued g) h k.val (fun i => ⟨d i,v i⟩) y)) x fee := by
  have eq : (fun y => out (msVector (N g hg) (Z g) (Teller.logNu 1) v y p h t)) =
      (fun y => out (∑ k : Fin (p+1), (t : ℂ)^k.val •
        (S g hg).ope (GraphCoefficients.issued g) h k.val (fun i => ⟨d i,v i⟩) y)) :=
    funext fun y => congrArg out (publicCrop g hg d v h p y t)
  rw [eq]

end YM.Integration.GradedFar.AppointedGraphMSVector
end

