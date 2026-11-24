import YangMills.WilsonProof.NativeSupport.ContinuumConstruction.ElectedPublicCorrelation
import YM.Integration.WilsonGraphAppointedPhysicalShapePrice

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

def clock (V : Vision E ξ) (Z : WilsonPrescription g.core) : ℝ → ℝ :=
  V.T Z

def frame (V : Vision E ξ) (Z : WilsonPrescription g.core) (r : ℝ) (d : ℕ) :
    (YangMills.maxwellReference g).sector d ≃ₗ[ℂ]
      (YangMills.hierarchy V.pupil.last V.pupil.P).Field d :=
  (YM.Maxwell.Free.fields E.paths.family.labels d).symm.trans (V.Post Z r d)

def inputs (V : Vision E ξ) (Z : WilsonPrescription g.core) (r : ℝ) {n : ℕ}
    (d : Fin n → ℕ) (v : (i : Fin n) → (YangMills.maxwellReference g).sector (d i)) :
    Fin n → (YangMills.hierarchy V.pupil.last V.pupil.P).Tag :=
  fun i => ⟨d i, frame V Z r (d i) (v i)⟩

theorem input (V : Vision E ξ) (Z : WilsonPrescription g.core) (r : ℝ) {n : ℕ}
    (d : Fin n → ℕ) (v : (i : Fin n) → (YangMills.maxwellReference g).sector (d i))
    (i : Fin n) : inputs V Z r d v i = ⟨d i, frame V Z r (d i) (v i)⟩ := rfl

theorem centerSeparated {n : ℕ} {r : ℝ} (hr : 0 < r) (o : YangMills.Spacetime)
    (x : YangMills.Points n) (hx : x ∈ YM.conf n) :
    (WithLp.toLp 2 (fun i : Fin n => o + r • x i) : YangMills.Points n) ∈ YM.conf n := by
  have scaled := Work.A05.smul_conf hr hx
  intro i j same
  apply scaled
  change o + r • x i = o + r • x j at same
  exact add_left_cancel same

theorem scalar (V : Vision E ξ) (Z : WilsonPrescription g.core) {n : ℕ}
    (viewer : Option (YangMills.hierarchy V.pupil.last V.pupil.P).Character)
    (d : Fin n → ℕ) (v : (i : Fin n) → (YangMills.maxwellReference g).sector (d i))
    {r : ℝ} (hr : 0 < r) (o : YangMills.Spacetime) (x : YangMills.Points n) (hx : x ∈ YM.conf n) :
    (YangMills.hierarchy V.pupil.last V.pupil.P).correlation viewer (inputs V Z r d v)
        (WithLp.toLp 2 (fun i : Fin n => o + r • x i)) =
      TrueCompact V.pupil.last (V.Post Z) viewer r o x v := by
  exact atTable (T' := spectator V.pupil.last viewer) d (labels (V.Post Z) r v)
    (spectate V.pupil.last viewer) (centerSeparated hr o x hx)


theorem positive (V : Vision E ξ) (Z : WilsonPrescription g.core) (Q : Perspective H Z true) :
    ∀ᶠ r in trail, 0 < clock V Z r :=
  (V.certificate Q).calendar.clock.positive

theorem included (V : Vision E ξ) (Z : WilsonPrescription g.core) (Q : Perspective H Z true)
    {d h : ℕ} (within : d ≤ h) :
    ∀ᶠ r in trail, ∀ u : (YangMills.maxwellReference g).sector d,
      frame V Z r h (XSpace.Normalize.up within u) =
        V.pupil.last.sector.derivatives.rise within (frame V Z r d u) :=
  Integration.WilsonGraphAppointedMixedShapeJets.included V.pupil.last (V.Post Z)
    (Integration.WilsonGraphAppointedStationaryPrices.adjacent Z V Q) within

end YM.Answer.ContinuumLimit.ElectedMeasurement


