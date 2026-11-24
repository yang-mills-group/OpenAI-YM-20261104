import YM.Integration.WilsonGraphAppointedPositionFrame
import YangMills.WilsonProof.NativeSupport.ContinuumConstruction.TableConjugation
import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedRealFieldColumns
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


theorem preCoefficientFixed {d : ℕ} (p : (YangMills.maxwellReference g).sector d) :
    (∀ m, (MvPolynomial.coeff m p.val).im = 0) ↔ XSpace.Normalize.reel d p = p := by
  constructor
  · intro hp
    apply Subtype.ext
    change MvPolynomial.map (starRingEnd ℂ) p.val = p.val
    apply MvPolynomial.ext
    intro m
    rw [MvPolynomial.coeff_map]
    exact Complex.conj_eq_iff_im.mpr (hp m)
  · intro hp m
    apply Complex.conj_eq_iff_im.mp
    have eq := congrArg (fun a : (YangMills.maxwellReference g).sector d => MvPolynomial.coeff m a.val) hp
    change MvPolynomial.coeff m (MvPolynomial.map (starRingEnd ℂ) p.val) = _ at eq
    simpa only [MvPolynomial.coeff_map] using eq

theorem preFieldReal (V : Vision E ξ) (Z : WilsonPrescription g.core)
    {lamp : Bool} (Q : Perspective H Z lamp) (d : ℕ) :
    ∀ᶠ r in trail, ∀ v : (YangMills.maxwellReference g).sector d,
      (∀ m, (MvPolynomial.coeff m v.val).im = 0) →
      V.pupil.S.conj V.pupil.last.room.kernel.spin d (preFrame V Z r d v) =
        preFrame V Z r d v := by
  filter_upwards [((V.certificate Q).spin d).1] with r orientedAt
  intro v coefficients
  have same := (preCoefficientFixed v).mp coefficients
  have mapped := orientedAt.2.1 v
  rw [same] at mapped
  exact mapped.symm

theorem preReal (V : Vision E ξ) (Z : WilsonPrescription g.core)
    {lamp : Bool} (Q : Perspective H Z lamp) :
    YangMills.MSbar.PositionReal (YangMills.hierarchy V.pupil.last V.pupil.P)
      (preFrame V Z) := by
  intro d
  filter_upwards [preFieldReal V Z Q d] with r fixedAt
  intro n fields realCoefficients x separated
  exact OriginalTableConjugation.fieldsReal V.pupil.S
    V.pupil.last.room.kernel.laws.toSymmetric V.pupil.last.room.kernel.spin separated
    (fun i => ⟨d, preFrame V Z r d (fields i)⟩)
    (fun i => fixedAt (fields i) (realCoefficients i))

end YM.Answer.ContinuumLimit.ElectedMeasurement

