import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.PositionStore
import YM.Integration.WilsonPositionPrescribedScreen
import YM.Integration.WilsonGraphAppointedMeasurementLaws
import YangMills.WilsonProof.NativeSupport.MSPhysicalAppointment
import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedAppointedConversionValid

noncomputable section

namespace YM.Answer.ContinuumLimit.ElectedMeasurement

open Function Filter Set Asymptotics PowerSeries
open Lattice RG MeasureTheory Wilson Extraction Climb Trace.Pilot
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato FullVolume Spec Table
open Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Structure1
open MS MS.Land MS.Fleet PhysMS PhysMS.Frame Next.UVStress OPE OPE.Orbits
open FVA2 FVA2.Register FVA2.Scale FVA2.Scale.Level
open SignedWilsonExpansion SignedWilsonExpansion.Belle SignedWilsonExpansion.Belle.Path SignedWilsonExpansion.Museum SignedWilsonExpansion.Kane
open SignedWilsonExpansion.Kane.Tilted SignedWilsonExpansion.Camera
open Integration.Election Integration.Election.Frames
open Order Spin SignedWilsonExpansion.StageG XSpace.Cirrus Entree Future
open Belfry Belle Dancer Belfry.ScaleFits Belfry.Classroom Scale Level GroupS
open Answer.ContinuumLimit Answer.ContinuumLimit.Vision
open Integration.GradedFar Integration.GradedFar.Tariff
open _root_.IssuedBridge
open scoped Topology BigOperators Classical ContDiff

open FVA2.GradedFar FVA2.Dframe
universe u
variable {g : YangMills.GaugeGroup} {H : g.core.Simple} {ε : ℝ}
variable {e : Axis} {O : OrderS g.core} {E : Construction.{u} H ε e O}
variable {ξ : Extraction.Order}

def preFrame (V : Vision E ξ) (Z : WilsonPrescription g.core) :
    YangMills.MSbar.PositionFrames (YangMills.hierarchy V.pupil.last V.pupil.P)
      (YangMills.maxwellReference g) :=
  fun r d => (Maxwell.Free.fields E.paths.family.labels d).symm.trans (V.Pre Z r d)

theorem numericalFrame (V : Vision E ξ) (Z : WilsonPrescription g.core)
    (Q : Perspective H Z true) (law : Integration.WilsonPositionHomogeneousCoefficients.Warrant Z)
    (d : ℕ) : ∀ᶠ r in trail, ∀ v : (YangMills.maxwellReference g).sector d,
      frame V Z r d v = preFrame V Z r d
        ((_root_.IssuedBridge.PostedNumericalAdjustment.filed Z law).value d (clock V Z r) v) := by
  filter_upwards [positive V Z Q, positiveRepresentative V Z Q d] with r hr measured
  intro v
  rw [_root_.IssuedBridge.PostedNumericalAdjustment.original Z law d hr]
  exact measured v

theorem filedPositionFrame (hg : g.IsSimple) (V : Vision E ξ)
    (Q : Perspective H (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) true) (d : ℕ) :
    let Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
    ∀ᶠ r in trail, ∀ v : (YangMills.maxwellReference g).sector d,
      frame V Z r d v = preFrame V Z r d
        ((_root_.IssuedBridge.PostedAppointedConversionValid.realized hg true).value d (clock V Z r) v) := by
  exact numericalFrame V (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) Q
    (Integration.WilsonPositionHomogeneousCoefficients.purchased
      (_root_.IssuedMaxwell.ElectedPrescription.issued g hg)
      (_root_.IssuedBridge.PostedAppointedConversionFields.elected hg true)) d


theorem preReport (V : Vision E ξ) (Z : WilsonPrescription g.core) (d : ℕ)
    {r : ℝ} (hr : 0 < r) :
    _root_.IssuedMaxwell.Reports.printed
      (Integration.WilsonPositionPrescribedScreen.hierarchy V.pupil.last (V.Pre Z) d r) =
    YangMills.MSbar.positionReport (YangMills.hierarchy V.pupil.last V.pupil.P)
      (preFrame V Z) r d := by
  funext n φ v
  exact Integration.WilsonPositionPrescribedScreen.actual V.pupil.last (V.Pre Z) d n φ v hr

theorem preIntegrable (V : Vision E ξ) (Z : WilsonPrescription g.core) (d n : ℕ)
    (φ : YangMills.SeparatedTest n) (v : Fin n → (YangMills.maxwellReference g).sector d)
    {r : ℝ} (hr : 0 < r) :
    MeasureTheory.Integrable (fun x => φ x * YangMills.MSbar.positionMoment
      (YangMills.hierarchy V.pupil.last V.pupil.P) (preFrame V Z) r d v x) :=
  _root_.YM.Test.smearing φ (Integration.WilsonPositionPrescribedScreen.smooth V.pupil.last (V.Pre Z) v hr)

theorem preFreeLimit (V : Vision E ξ) (Z : WilsonPrescription g.core)
    (Q : Perspective H Z true) (d n : ℕ) (φ : YangMills.SeparatedTest n)
    (v : Fin n → (YangMills.maxwellReference g).sector d) :
    Tendsto (fun r => YangMills.MSbar.positionReport
      (YangMills.hierarchy V.pupil.last V.pupil.P) (preFrame V Z) r d n φ v) trail
      (𝓝 (YangMills.MSbar.Position.free (YangMills.maxwellReference g) d n φ v)) := by
  let a := fun i : Fin n => (Maxwell.Free.fields E.paths.family.labels d).symm (v i)
  have purchased := Integration.WilsonOrdinaryPositionPoll.tends V.pupil.last (V.Pre Z)
    (V.certificate Q).leading φ a
  have free : _root_.YM.Test.applyTo φ (PhysMS.WickGoal (C := E.paths.family) (d := fun _ => d) a) =
      YangMills.MSbar.Position.free (YangMills.maxwellReference g) d n φ v := by
    change _root_.YM.Test.applyTo φ _ = _root_.YM.Test.applyTo φ _
    congr 1
    funext x
    exact Integration.WilsonPositionPrescribedScreen.zero d n v x
  rw [free] at purchased
  exact purchased

theorem preScreen (hg : g.IsSimple) (V : Vision E ξ)
    (Q : Perspective H (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) true) (d : ℕ) :
    let Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
    let P := (_root_.IssuedMaxwell.ElectedPrescription.prior g hg).val
    ∀ᶠ r in trail, (P.screen d).read (YangMills.MSbar.positionReport
      (YangMills.hierarchy V.pupil.last V.pupil.P) (preFrame V Z) r d) =
      (P.screen d).read (YangMills.MSbar.Position.free (YangMills.maxwellReference g) d) := by
  let Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
  let menu := _root_.IssuedMaxwell.ElectedPrescription.prior g hg
  filter_upwards [(V.certificate Q).determined d, RG17.positiveLength] with r screen hr
  have h := congrArg Subtype.val screen
  rw [(_root_.IssuedMaxwell.ElectedPrescription.original g hg).2.1] at h
  rw [_root_.IssuedMaxwell.PositionStore.reported menu.val menu.property,
      _root_.IssuedMaxwell.PositionStore.reported menu.val menu.property,
      preReport V Z d hr, _root_.IssuedMaxwell.Reports.free g d] at h
  exact h

end YM.Answer.ContinuumLimit.ElectedMeasurement
