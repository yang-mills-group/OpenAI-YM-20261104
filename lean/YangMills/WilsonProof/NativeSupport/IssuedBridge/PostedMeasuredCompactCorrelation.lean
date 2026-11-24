import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedTranslatedExpansion
import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedOneFrameMaxwell
import YM.Integration.WilsonOriginalPhysicalCoordinateBox
set_option autoImplicit false
set_option maxRecDepth 4096
noncomputable section
universe u
namespace IssuedBridge.PostedMeasuredCompactCorrelation
open YangMills YangMills.Wilson
open YM YM.Integration YM.Spec YM.OPE YM.OPE.Orbits YM.Maxwell YM.Maxwell.Free
open WilsonOneFrameMixedMaxwell WilsonPositionHomogeneousFrame
open Climb Lattice RG PhysMS Trace.Pilot Next.Extract PhysicalNext.Repeat.Legato RG17 XSpace XSpace.Normalize FVA2 FVA2.Register
open FixedFields
open Function Filter Set
open scoped Topology BigOperators Classical

variable {g : GaugeGroup} {R : Run g.core}
variable {p : Extraction.Order} {S : Table R.family.book}
variable {F : Final R.family p S} {Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin}
variable {L : EveryPhase.Almanac F} {J : ℝ → PhysMS.tower S}
variable {arch : Trace.Terrace.Arch R.family} {Y : (Bel R.family.book).Hierarchy}
variable {ℓ : Ultrafilter (ℕ × ℕ)} {simple : g.core.Simple} {cohort : Ultrafilter (ℕ × ℕ) → Prop}
variable {n : ℕ}
variable (run : WilsonViewerElectedHierarchy.Selected.{u} F L Q J Y arch ℓ simple cohort)
variable (Z : WilsonPrescription g.core)
local notation "C" => R.family
local notation "B" => maxwellReference g
local notation "T" => hierarchy F Q
local notation "H" => homogeneous F J Z
local notation "θ" => reading F J Z
open scoped ContDiff
def leaves (d : Fin n → ℕ) (v : (i : Fin n) → (B).sector (d i)) : MaxwellSlots R.family d :=
  fun i => (YM.Maxwell.Free.fields R.family.labels (d i)).symm (v i)

include run in
theorem original (d : Fin (n+1) → ℕ) (v : (i : Fin (n+1)) → (B).sector (d i))
    (M : MSbar.Coefficients B) (A : Matching.Conversion B) (μ : Matching.Measurement B T)
    (calibrated : μ.frame = fun r d => (YM.Maxwell.Free.fields R.family.labels d).symm.trans (H r d))
    (stopped : μ.clock = θ) (thermal : Coupling g.core θ)
    (smooth : ∀ k, ContDiffOn ℝ ∞ (fun x => A.correlation M k (fun i => ⟨d i,v i⟩) x) (conf (n+1)))
    (Dtest : WilsonOriginalCompactPoseCover.Box (n+1) (n*4+3+1) → ℕ)
    (earned : WilsonOriginalGlobalViewerShape.Tested (F:=F) (J:=J) Z d (leaves (R:=R) d v)
      (fun k x => A.correlation M k (fun i => ⟨d i,v i⟩) x) Dtest)
    (phase : Option (T).Character) (o : Spacetime) :
    Matching.HasExpansion 0 μ.clock (fun r x =>
      (T).correlation phase (μ.inputs r fun i => ⟨d i,v i⟩) (WithLp.toLp 2 fun i => o + r • x i))
      (fun k x => A.correlation M k (fun i => ⟨d i,v i⟩) x) := by
  have coord : (Fin (n*4+3+1) → ℝ) ≃L[ℝ] YM.Points (n+1) := by
    rw [show n*4+3+1 = (n+1)*4 by omega]
    exact WilsonOriginalPhysicalCoordinateBox.coordinates _
  rw [stopped]
  have tags (r : ℝ) : μ.inputs r (fun i => ⟨d i,v i⟩) =
      fun i => ⟨d i,H r (d i) (leaves (R:=R) d v i)⟩ := by
    funext i
    change Sigma.mk (d i) (μ.frame r (d i) (v i)) = _
    rw [calibrated]
    rfl
  have actual : (fun r x => (T).correlation phase (μ.inputs r fun i => ⟨d i,v i⟩)
      (WithLp.toLp 2 fun i => o + r • x i)) =
      (fun r (x : YM.Points (n+1)) => S.classMoment (spectator F phase) d
        (points fun i => o + r • x i) (fun i => H r (d i) (leaves (R:=R) d v i))) := by
    funext r x
    rw [tags]
    rfl
  rw [actual]
  exact PostedTranslatedExpansion.original run Z d (leaves (R:=R) d v) thermal coord _ smooth Dtest earned phase o
end IssuedBridge.PostedMeasuredCompactCorrelation
