import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedAppointedFieldBank
import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedAxisFieldColumns
import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedHomogeneousFieldColumns
import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedRealFieldColumns
import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedOriginalFieldInverse
import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedRealFiledCoupling
import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedAppointedFieldCorrelation
noncomputable section
namespace IssuedBridge.PostedAppointedConversion
open YangMills YangMills.Wilson
open YM YM.Integration YM.Spec YM.OPE YM.OPE.Orbits YM.Maxwell YM.Maxwell.Free
open WilsonOneFrameMixedMaxwell WilsonPositionHomogeneousFrame
open Climb Lattice RG PhysMS Trace.Pilot Next.Extract PhysicalNext.Repeat.Legato RG17 XSpace XSpace.Normalize FVA2 FVA2.Register
open FixedFields
open Function Filter Set
open scoped Topology BigOperators Classical

variable {g : GaugeGroup} {R : Run g.core}
variable {simple : g.core.Simple} (Z : WilsonPrescription g.core)
open MS MS.Land MS.Fleet FVA2.Scale WilsonViewerReportingGrid WilsonThermometerWeakMeasuredSeries
open WilsonViewerGridPins WilsonViewerAlignedResidual WilsonViewerElectedHierarchy
open WilsonPositionThermometerCapStation WilsonPositionCapTransport WilsonLimitConstruction
open PostedMeasuredCompactCorrelation (leaves)
variable (raw : MS_Data g.core (Position.OpenAxis.Plot (Press.portDeck g.core)))
variable {σ : Prescription (Press.portDeck g.core)} {dial : Bool} (matched : Main.Match Z simple raw σ dial)

open YM.FVA2.Scale YM.MS YM.MS.Fleet YM.MS.Land YangMills.Matching
def filed (μ : ℝ) : YangMills.Matching.Conversion (maxwellReference g) where
  f := PostedRealFiledCoupling.coefficient Z raw μ
  f_zero := (PostedRealFiledCoupling.original Z raw matched μ).2.1
  f_one := (PostedRealFiledCoupling.original Z raw matched μ).2.2
  Z := PostedAppointedFieldBank.column Z raw μ
  Zinv := fun d k => PowerSeries.coeff k
    (PowerSeries.invOfUnit (Measure.Z Z.scheme Z.criterion μ raw d) 1)
  leading := fun d => (PostedAppointedFieldBank.original Z raw matched μ d).1
  nested := PostedAppointedFieldBank.nested Z raw matched μ
  preservesGrade := PostedHomogeneousFieldColumns.original Z raw matched μ
  preservesUnit := fun d => (PostedAppointedFieldBank.original Z raw matched μ d).2.2.2
  real := PostedRealFieldColumns.original Z raw matched μ
  signedAxes := PostedAxisFieldColumns.original Z raw matched μ
  leftInverse := fun d k => (PostedOriginalFieldInverse.original Z raw matched μ d k).1
  rightInverse := fun d k => (PostedOriginalFieldInverse.original Z raw matched μ d k).2

theorem original (μ : ℝ) (official : YangMills.MSbar.Coefficients (maxwellReference g))
    {n h : ℕ} (d : Fin n → ℕ) (v : (i : Fin n) → (maxwellReference g).sector (d i))
    (within : ∀ i, d i ≤ h) (x : Stage n) (k : ℕ)
    (forest : ∀ j (b : (i : Fin n) → (maxwellReference g).sector (d i)),
      Equator.wave μ raw h n x j (fun i => XSpace.Normalize.up (within i) (b i)) =
        official.correlation n j (fun i => ⟨d i,b i⟩) x.val) :
    Jury.fxt (Measure.outlook Z.scheme Z.criterion h) x.val k
      (commonCaps (leaves (R:=R) d v) within) =
      (filed Z raw matched μ).correlation official k (fun i => ⟨d i,v i⟩) x.val := by
  classical
  rw [PostedAppointedFieldCorrelation.original (R:=R) Z raw matched μ d v within x k]
  unfold YangMills.Matching.Conversion.correlation
  apply Finset.sum_congr rfl
  intro ν _
  apply Finset.sum_congr rfl
  intro j _
  dsimp only
  split_ifs
  · (rw [forest]; rfl)
  · rfl

end IssuedBridge.PostedAppointedConversion
end
