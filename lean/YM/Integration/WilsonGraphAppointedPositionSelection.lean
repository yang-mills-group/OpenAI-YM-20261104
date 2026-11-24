import YM.Integration.WilsonGraphAppointedPositionNormalization

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

theorem preNormalized (hg : g.IsSimple) (V : Vision E ξ)
    (Q : Perspective H (_root_.IssuedMaxwell.ElectedPrescription.issued g hg) true) :
    let Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
    let menu := _root_.IssuedMaxwell.ElectedPrescription.prior g hg
    YangMills.MSbar.PositionNormalized (YangMills.hierarchy V.pupil.last V.pupil.P)
      menu.val (preFrame V Z) := by
  let Z := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
  constructor
  · exact fun d n φ v => preFreeLimit V Z Q d n φ v
  · intro d
    have positive : ∀ᶠ r : ℝ in trail, 0 < r := self_mem_nhdsWithin
    filter_upwards [positive, preScreen hg V Q d, preJacobian hg V Q d] with r hr hscreen hjac
    exact ⟨fun n φ v => preIntegrable V Z d n φ v hr, hscreen, hjac⟩

theorem prePinIncluded (V : Vision E ξ) (Z : WilsonPrescription g.core)
    (Q : Perspective H Z true) {d e : ℕ} (h : d ≤ e) :
    ∀ᶠ r in trail, ∀ v : (YangMills.maxwellReference g).sector d,
      V.pupil.S.pin e (preFrame V Z r e (XSpace.Normalize.up h v)) =
        V.pupil.S.pin d (preFrame V Z r d v) := by
  filter_upwards [(V.certificate Q).inclusion d e h] with r hr
  intro v
  have inc := (hr v).2
  change V.pupil.S.pin e (window Z V false r e (XSpace.Normalize.up h v)) =
    V.pupil.S.pin d (window Z V false r d v)
  rw [inc]
  exact V.pupil.last.sector.derivatives.stays
    (spectate V.pupil.last none).laws.toSymmetric (spectate_ready V.pupil.last none) h _

theorem preNested (V : Vision E ξ) (Z : WilsonPrescription g.core)
    (Q : Perspective H Z true) :
    YangMills.MSbar.PositionNested (YangMills.hierarchy V.pupil.last V.pupil.P)
      (preFrame V Z) := by
  intro d e v w same
  rcases le_total d e with h | h
  · have eq : XSpace.Normalize.up h v = w := Subtype.ext same
    filter_upwards [prePinIncluded V Z Q h] with r hr
    change V.pupil.S.pin d (preFrame V Z r d v) = V.pupil.S.pin e (preFrame V Z r e w)
    rw [← eq]
    exact (hr v).symm
  · have eq : XSpace.Normalize.up h w = v := Subtype.ext same.symm
    filter_upwards [prePinIncluded V Z Q h] with r hr
    change V.pupil.S.pin d (preFrame V Z r d v) = V.pupil.S.pin e (preFrame V Z r e w)
    rw [← eq]
    exact hr w

end YM.Answer.ContinuumLimit.ElectedMeasurement

