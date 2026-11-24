import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedNamedCorrelation
import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedMeasuredCompactCorrelation
set_option autoImplicit false
set_option maxRecDepth 4096
noncomputable section
universe u
namespace IssuedBridge.PostedAppointedPinFrame
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
open MS MS.Land MS.Fleet FVA2.Scale WilsonViewerReportingGrid WilsonThermometerWeakMeasuredSeries
open WilsonViewerGridPins WilsonViewerAlignedResidual WilsonViewerElectedHierarchy
open WilsonPositionThermometerCapStation WilsonPositionCapTransport WilsonLimitConstruction
open PostedMeasuredCompactCorrelation (leaves)
variable (raw : MS_Data g.core (Position.OpenAxis.Plot (Press.portDeck g.core)))
variable {σ : Prescription (Press.portDeck g.core)} {dial : Bool} (matched : Main.Match Z simple raw σ dial)
include run matched in
theorem original (ν : ℝ) {cap : ℕ} (d : Fin n → ℕ) (within : ∀ i, d i ≤ cap)
    (v : (i : Fin n) → (B).sector (d i))
    (M : MSbar.Coefficients B) (A : Matching.Conversion B) (μ : Matching.Measurement B T)
    (calibrated : μ.frame = fun r d => (YM.Maxwell.Free.fields R.family.labels d).symm.trans (H r d))
    (stopped : μ.clock = θ) (thermal : Coupling g.core θ) (P : Report F ℓ cap θ)
    (price : ∀ p : ℕ, ∃ (W : Finset E4) (q : ℕ), WilsonThermometerWeakSignedJets.high 0 p ≤ q ∧
      WilsonPositionScaleLawPowerPinLimit.Price Z raw ν (leaves (R:=R) d v) within P W
        (WilsonThermometerWeakSignedJets.high 0 p+1) q)
    (fields : ∀ k x, x ∈ conf n →
      Jury.fxt (Measure.outlook Z.scheme Z.criterion cap) x k (commonCaps (leaves (R:=R) d v) within) =
      A.correlation M k (fun i => ⟨d i,v i⟩) x)
    (phase : Option (T).Character) (o : Spacetime) :
    Matching.HasExpansion 0 μ.clock (fun r x =>
      (T).correlation phase (μ.inputs r fun i => ⟨d i,v i⟩) (WithLp.toLp 2 fun i => o + r • x i))
      (fun k x => A.correlation M k (fun i => ⟨d i,v i⟩) x) := by
  rw [stopped]
  have paid := PostedFinitePinCorrelation.original run Z raw matched ν d within thermal P
    (leaves (R:=R) d v) price phase
  apply PostedNamedCorrelation.original M A _ _ fields
  apply PostedTranslatedExpansion.onConf paid
  intro r hr x hx
  have tags : μ.inputs r (fun i => ⟨d i,v i⟩) =
      fun i => ⟨d i,H r (d i) (leaves (R:=R) d v i)⟩ := by
    funext i
    change Sigma.mk (d i) (μ.frame r (d i) (v i)) = _
    rw [calibrated]
    rfl
  rw [tags]
  exact (WilsonOriginalTranslatedCorrelation.original F phase (H r) d (leaves (R:=R) d v) r hr o hx).symm
end IssuedBridge.PostedAppointedPinFrame
