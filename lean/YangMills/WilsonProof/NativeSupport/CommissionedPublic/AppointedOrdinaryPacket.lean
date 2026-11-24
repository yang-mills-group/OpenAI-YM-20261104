import YM.Integration.WilsonGraphAppointedMeasurementLaws
import YangMills.WilsonProof.NativeSupport.MatchingSpec
import YangMills.WilsonProof.NativeSupport.MeasuredShapeJets
import YM.OPE.Orbits.System

namespace YM.Answer.ContinuumLimit.AppointedOrdinaryPacket

noncomputable section
set_option maxHeartbeats 2400000
open YM
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
open YM.Maxwell.Free
open OPE OPE.Orbits
open scoped ContDiff

universe u
variable {g : YangMills.GaugeGroup} {s : g.core.Simple} {ε : ℝ}
variable {e : Axis} {O : OrderS g.core} {E : Construction.{u} s ε e O} {ξ : Extraction.Order}

private abbrev letters {n : ℕ} (d : Fin n → ℕ)
    (v : (i : Fin n) → (YangMills.maxwellReference g).sector (d i)) :
    Fin n → (Σ e : ℕ, (YangMills.maxwellReference g).sector e) :=
  fun i => ⟨d i, v i⟩

theorem coefficientMap (V : Vision E ξ) {I : Type} [Fintype I]
    (d : I → ℕ) (j : ℕ) (c : (YangMills.hierarchy V.pupil.last V.pupil.P).Channel j)
    (x : I → YangMills.Spacetime) (o : YangMills.Spacetime) :
    ∃ coeff : MultilinearMap ℂ
      (fun i => (YangMills.hierarchy V.pupil.last V.pupil.P).Field (d i)) ℂ,
      ∀ v, (YangMills.hierarchy V.pupil.last V.pupil.P).coefficient
        (fun i => ⟨d i, v i⟩) j c x o = coeff v := by
  let Q := V.pupil.P
  let grade := (Q.knife j).codRestrict (Q.stratum j) (fun a => Q.knife_mem j a)
  let column := (Q.basis j).coord c ∘ₗ grade
  exact ⟨column.compMultilinearMap (checkReal Q.port Q.law Q.continuum j x o), fun _ => rfl⟩

def measurement (hg : g.IsSimple) (V : Vision E ξ) (N : YM.FVA2.Register.WilsonPrescription g.core)
    (Q : Perspective s N true) :
    YangMills.Matching.Measurement (YangMills.maxwellReference g)
      (YangMills.hierarchy V.pupil.last V.pupil.P) where
  clock := (ElectedMeasurement.publicMeasurement hg V N Q).clock
  positive := (ElectedMeasurement.publicMeasurement hg V N Q).positive
  oneLoop := (ElectedMeasurement.publicMeasurement hg V N Q).oneLoop
  frame := (ElectedMeasurement.publicMeasurement hg V N Q).frame
  nested := (ElectedMeasurement.publicMeasurement hg V N Q).nested
  frameAxes := (ElectedMeasurement.publicMeasurement hg V N Q).frameAxes
  unit := (ElectedMeasurement.publicMeasurement hg V N Q).unit
  includeField := ElectedMeasurement.includeField V
  includeLabel := ElectedMeasurement.includeLabel V
  includeInsertion := ElectedMeasurement.includeInsertion V
  multilinear := ElectedMeasurement.multilinear V
  coefficientMultilinear := fun d j c x _ o => coefficientMap V d j c x o

theorem clock (hg : g.IsSimple) (V : Vision E ξ) (N : YM.FVA2.Register.WilsonPrescription g.core)
    (Q : Perspective s N true) : (measurement hg V N Q).clock = V.T N := rfl

theorem frame (hg : g.IsSimple) (V : Vision E ξ) (N : YM.FVA2.Register.WilsonPrescription g.core)
    (Q : Perspective s N true) : (measurement hg V N Q).frame = ElectedMeasurement.frame V N := rfl

theorem packet (hg : g.IsSimple) (V : Vision E ξ) (N : YM.FVA2.Register.WilsonPrescription g.core)
    (Q : Perspective s N true) {n : ℕ} (h : ℕ) (d : Fin n → ℕ)
    (v : (i : Fin n) → (YangMills.maxwellReference g).sector (d i))
    (r : ℝ) (o : YangMills.Spacetime) (x : YangMills.Points n) :
    (measurement hg V N Q).wilsonOPE r h (letters d v) o x =
      (ElectedMeasurement.frame V N r h).symm
        (V.pupil.P.packet h (fun i => o + r • x i)
          (fun i => ElectedMeasurement.frame V N r (d i) (v i)) o) := by
  let sites : Fin n → YangMills.Spacetime := fun i => o + r • x i
  let fields := fun i => ElectedMeasurement.frame V N r (d i) (v i)
  have each (j : Fin (h+1)) :
      (∑ c : V.pupil.P.channels j.val, V.pupil.P.coef j.val c sites fields o •
        V.pupil.last.sector.derivatives.rise (Nat.le_of_lt_succ j.isLt) (V.pupil.P.actor j.val c)) =
      V.pupil.last.sector.derivatives.rise (Nat.le_of_lt_succ j.isLt)
        (V.pupil.P.fresh j.val sites o fields) := by
    rw [← V.pupil.P.assemble j.val sites fields o]
    simp only [map_sum, map_smul]
  exact congrArg (ElectedMeasurement.frame V N r h).symm
    (Finset.sum_congr rfl fun j _ => each j)

theorem emptyPacket (hg : g.IsSimple) (V : Vision E ξ) (N : YM.FVA2.Register.WilsonPrescription g.core)
    (Q : Perspective s N true) (h : ℕ) (d : Fin 0 → ℕ)
    (v : (i : Fin 0) → (YangMills.maxwellReference g).sector (d i))
    (r : ℝ) (o : YangMills.Spacetime) (x : YangMills.Points 0) :
    (measurement hg V N Q).wilsonOPE r h (letters d v) o x =
      (ElectedMeasurement.frame V N r h).symm
        (V.pupil.P.packet h (fun i => o + r • x i)
          (fun i => ElectedMeasurement.frame V N r (d i) (v i)) o) :=
  packet hg V N Q h d v r o x

open YangMills.Matching

/-- The coordinate expenses apply to the full real derivative tensors of the actual
public packet and coefficient crop. The same finite sum works for every output covector. -/
theorem fullDualJet (hg : g.IsSimple) (V : Vision E ξ) (N : YM.FVA2.Register.WilsonPrescription g.core)
    (Q : Perspective s N true) {n : ℕ} (h p j : ℕ) (d : Fin n → ℕ)
    (v : (i : Fin n) → (YangMills.maxwellReference g).sector (d i))
    (M : YangMills.MSbar.Coefficients (YangMills.maxwellReference g))
    (S : Conversion (YangMills.maxwellReference g)) (r : ℝ)
    (o : YangMills.Spacetime) (x : YangMills.Points n)
    {β : Type*} [Fintype β] (basis : β → (YangMills.maxwellReference g).sector h)
    (fees : β → ℝ) :
    let a := letters d v
    let H := measurement hg V N Q
    let physical := fun y : YangMills.Points n => H.wilsonOPE r h a o y
    let predicted := fun y : YangMills.Points n =>
      ∑ k : Fin (p+1), (H.clock r : ℂ)^k.val • S.ope M h k.val a y
    let size := (∏ i, sectorMass (v i)) * |H.clock r|^(p+1)
    (∀ out : (YangMills.maxwellReference g).sector h →ₗ[ℂ] ℂ,
      ContDiffAt ℝ j (fun y => out (physical y)) x ∧
      ContDiffAt ℝ j (fun y => out (predicted y)) x) →
    (∀ l ≤ j, ∃ rows : β → ContinuousMultilinearMap ℝ (fun _ : Fin l => YangMills.Points n) ℂ,
      (∀ b, ‖rows b‖ ≤ fees b * size) ∧
      ∀ out : (YangMills.maxwellReference g).sector h →ₗ[ℂ] ℂ,
        iteratedFDeriv ℝ l (fun y => out (physical y) - out (predicted y)) x =
          ∑ b, out (basis b) • rows b) →
    ∀ out : (YangMills.maxwellReference g).sector h →ₗ[ℂ] ℂ,
      (∀ w, ‖out w‖ ≤ sectorMass w) →
      shapeJetEstimateAt j (fun y => out (physical y)) (fun y => out (predicted y))
        x ((∑ b, sectorMass (basis b) * fees b) * size) := by
  intro a H physical predicted size smooth tensor out bounded
  refine ⟨(smooth out).1, (smooth out).2, ?_⟩
  intro l hl
  obtain ⟨rows, paid, components⟩ := tensor l hl
  rw [components out]
  calc
    ‖∑ b, out (basis b) • rows b‖ ≤ ∑ b, ‖out (basis b) • rows b‖ := norm_sum_le _ _
    _ ≤ ∑ b, sectorMass (basis b) * (fees b * size) := by
      apply Finset.sum_le_sum
      intro b _
      rw [norm_smul]
      exact mul_le_mul (bounded (basis b)) (paid b) (norm_nonneg _) (sectorMass_nonneg _)
    _ = (∑ b, sectorMass (basis b) * fees b) * size := by
      simp only [Finset.sum_mul, mul_assoc]

end
end YM.Answer.ContinuumLimit.AppointedOrdinaryPacket

