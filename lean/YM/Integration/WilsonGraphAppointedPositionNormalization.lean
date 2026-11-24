import YM.Integration.WilsonGraphAppointedPositionFrame
import YM.Integration.WilsonGraphAppointedZeroScreen
import YM.Integration.WilsonGraphFiniteScreenReaders
import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.Tangents
set_option autoImplicit false
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


theorem preNativeZero (hg : g.IsSimple) (V : Vision E ξ)
    (Q : Perspective H (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) true) (d : ℕ) :
    let Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
    let menu := _root_.IssuedMaxwell.ElectedPrescription.prior g hg
    ∀ᶠ r in trail, Fray.SetEq
      ((_root_.IssuedMaxwell.PositionStore.original menu.val menu.property).measure d)
      0 (Integration.WilsonPositionPrescribedScreen.hierarchy V.pupil.last (V.Pre Z) d r) := by
  filter_upwards [(V.certificate Q).determined d] with r screen
  rw [(_root_.IssuedMaxwell.ElectedPrescription.original g hg).2.1] at screen
  simpa only [Fray.SetEq, stand0, Screen.recruit_one] using screen

theorem preChangedReport (V : Vision E ξ) (Z : WilsonPrescription g.core) (d : ℕ)
    {r : ℝ} (hr : 0 < r) (X : Change g.core d) :
    _root_.IssuedMaxwell.Reports.printed (recruit (stand X)
      (Integration.WilsonPositionPrescribedScreen.hierarchy V.pupil.last (V.Pre Z) d r)) =
    fun n φ v => YangMills.MSbar.positionReport (YangMills.hierarchy V.pupil.last V.pupil.P)
      (preFrame V Z) r d n φ (fun i => v i + (show (YangMills.maxwellReference g).sector d from X.val (v i))) := by
  funext n φ v
  have report := congrFun (congrFun (congrFun (preReport V Z d hr) n) φ) (stand X ∘ v)
  change _root_.IssuedMaxwell.Reports.printed
    (Integration.WilsonPositionPrescribedScreen.hierarchy V.pupil.last (V.Pre Z) d r) n φ (stand X ∘ v) = _
  have forms : (stand X ∘ v) = (fun i => (show (YangMills.maxwellReference g).sector d from v i) + (show (YangMills.maxwellReference g).sector d from X.val (v i))) := by
    funext i
    rfl
  exact report.trans (congrArg
    (fun fields => YangMills.MSbar.positionReport (YangMills.hierarchy V.pupil.last V.pupil.P)
      (preFrame V Z) r d n φ fields) forms)

theorem preLocallyUnique (hg : g.IsSimple) (V : Vision E ξ)
    (Q : Perspective H (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) true) :
    let Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
    let menu := _root_.IssuedMaxwell.ElectedPrescription.prior g hg
    YangMills.MSbar.PositionLocallyUnique (YangMills.hierarchy V.pupil.last V.pupil.P)
      menu.val (preFrame V Z) := by
  let Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
  let menu := _root_.IssuedMaxwell.ElectedPrescription.prior g hg
  let bank := _root_.IssuedMaxwell.PositionStore.original menu.val menu.property
  change YangMills.MSbar.PositionLocallyUnique (YangMills.hierarchy V.pupil.last V.pupil.P) menu.val (preFrame V Z)
  intro d X permitted weak
  let b (r : ℝ) : Change g.core d := if h : X r ∈ Change g.core d then ⟨X r, h⟩ else 0
  have agrees : ∀ᶠ r in trail, (b r).val = X r := by
    filter_upwards [permitted] with r allowed
    have native : (X r : FieldEnd g.core d) ∈ Change g.core d :=
      (_root_.IssuedMaxwell.Tangents.original (X r)).mpr allowed
    have eq : b r = ⟨X r, native⟩ := by
      dsimp only [b]
      split
      · rfl
      · rename_i h
        exact (h native).elim
    exact congrArg Subtype.val eq
  have near := guideOfEveryReader trail b (fun v out => (weak v out).congr' (by
    filter_upwards [agrees] with r ar
    exact congrArg (fun F : FieldEnd g.core d => out (F v)) ar.symm))
  have unique := Integration.WilsonPositionPrescribedScreen.zeroIsUnique V.pupil.last
    (V.Pre Z) (V.certificate Q).leading bank d (preNativeZero hg V Q d) b near
  filter_upwards [unique, agrees, RG17.positiveLength] with r localRule agreesAt hr
  have readRule : Fray.SetEq (bank.measure d) (b r)
      (Integration.WilsonPositionPrescribedScreen.hierarchy V.pupil.last (V.Pre Z) d r) ↔
      (menu.val.screen d).read (fun n φ v => YangMills.MSbar.positionReport
        (YangMills.hierarchy V.pupil.last V.pupil.P) (preFrame V Z) r d n φ
        (fun i => v i + X r (v i))) =
      (menu.val.screen d).read (YangMills.MSbar.Position.free (YangMills.maxwellReference g) d) := by
    unfold Fray.SetEq
    constructor
    · intro h
      have hv := congrArg Subtype.val h
      rw [_root_.IssuedMaxwell.PositionStore.reported menu.val menu.property,
          _root_.IssuedMaxwell.PositionStore.reported menu.val menu.property,
          preChangedReport V Z d hr (b r), _root_.IssuedMaxwell.Reports.free g d, agreesAt] at hv
      exact hv
    · intro h
      apply Subtype.ext
      rw [_root_.IssuedMaxwell.PositionStore.reported menu.val menu.property,
          _root_.IssuedMaxwell.PositionStore.reported menu.val menu.property,
          preChangedReport V Z d hr (b r), _root_.IssuedMaxwell.Reports.free g d, agreesAt]
      exact h
  refine readRule.symm.trans (localRule.trans ?_)
  constructor
  · intro h
    rw [← agreesAt, h]
    rfl
  · intro h
    apply Subtype.ext
    rw [agreesAt, h]
    rfl

theorem preJacobian (hg : g.IsSimple) (V : Vision E ξ)
    (Q : Perspective H (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) true) (d : ℕ) :
    let Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
    let menu := _root_.IssuedMaxwell.ElectedPrescription.prior g hg
    ∀ᶠ r in trail, ∀ Y : FieldEnd g.core d,
      YangMills.MSbar.Position.IsChange (_root_.IssuedMaxwell.Reference.issued g) d Y →
      ∃! X : FieldEnd g.core d,
        YangMills.MSbar.Position.IsChange (_root_.IssuedMaxwell.Reference.issued g) d X ∧
        (menu.val.screen d).read (YangMills.MSbar.Position.variation
          (YangMills.MSbar.positionReport (YangMills.hierarchy V.pupil.last V.pupil.P)
            (preFrame V Z) r d) X) = Y := by
  let Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
  let menu := _root_.IssuedMaxwell.ElectedPrescription.prior g hg
  let bank := _root_.IssuedMaxwell.PositionStore.original menu.val menu.property
  have invertible := Integration.WilsonPositionPrescribedScreen.slopeAtZero V.pupil.last
    (V.Pre Z) (V.certificate Q).leading bank d (preNativeZero hg V Q d)
  filter_upwards [invertible, RG17.positiveLength] with r bij hr
  let pred := Integration.WilsonPositionPrescribedScreen.hierarchy V.pupil.last (V.Pre Z) d r
  have readSlope (T : Change g.core d) :
      (slope (bank.measure d) 0 pred T).val =
      (menu.val.screen d).read (YangMills.MSbar.Position.variation
        (YangMills.MSbar.positionReport (YangMills.hierarchy V.pupil.last V.pupil.P)
          (preFrame V Z) r d) T.val) := by
    change ((bank.measure d).D (tang (stand (0 : Change g.core d)) T.val pred)).val = _
    rw [stand0, XSpace.Normalize.tangent, _root_.IssuedMaxwell.PositionStore.reported menu.val menu.property,
        _root_.IssuedMaxwell.Reports.variation, preReport V Z d hr]
  intro Y allowed
  let target : Change g.core d := ⟨Y, (_root_.IssuedMaxwell.Tangents.original Y).mpr allowed⟩
  obtain ⟨T, hT⟩ := bij.surjective target
  refine ⟨T.val, ⟨(_root_.IssuedMaxwell.Tangents.original T.val).mp T.property,
    (readSlope T).symm.trans (congrArg Subtype.val hT)⟩, ?_⟩
  intro X hX
  let X' : Change g.core d := ⟨X, (_root_.IssuedMaxwell.Tangents.original X).mpr hX.1⟩
  have value : slope (bank.measure d) 0 pred X' = target := Subtype.ext ((readSlope X').trans hX.2)
  exact congrArg Subtype.val (bij.injective (value.trans hT.symm))

end YM.Answer.ContinuumLimit.ElectedMeasurement
