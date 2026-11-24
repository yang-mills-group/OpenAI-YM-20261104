import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedScreenedReparametrization
import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedOriginalGroundGraph
import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedFieldSubstitution
noncomputable section
namespace IssuedBridge.PostedPositionPrefixSmearing
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

open YangMills.MSbar
local notation "B" => maxwellReference g
local notation "W" => PostedPositionConversion.filed Z raw matched




open MeasureTheory

theorem original (μ : ℝ) (M : Coefficients (maxwellReference g))
    (cofiled : ∀ (n d k : ℕ) (x : Stage n) (u : Fin n → (maxwellReference g).sector d),
      M.correlation n k (fun i => ⟨d, u i⟩) x.val = Equator.wave μ raw d n x k u)
    (d k r n : ℕ) (A : Fin (r+1) → YangMills.MSbar.Position.EndAt (maxwellReference g) d)
    (φ : YangMills.SeparatedTest n) (v : Fin n → (maxwellReference g).sector d) :
    Integrable (fun x => φ x * YangMills.MSbar.Position.momentThrough M d k r A n v x) := by
  apply YM.Test.smearing φ
  unfold YangMills.MSbar.Position.momentThrough
  apply continuousOn_finsetSum
  intro ν _
  dsimp only
  by_cases within : (∑ i, (ν i).val) ≤ k
  · simp only [if_pos within]
    apply (Reg.CoverTest.measurable μ raw (k-∑ i, (ν i).val) (fun i => A (ν i) (v i))).congr
    intro x hx
    exact cofiled n d _ ⟨x,hx⟩ _
  · simp only [if_neg within]
    exact continuousOn_const

end IssuedBridge.PostedPositionPrefixSmearing
end
