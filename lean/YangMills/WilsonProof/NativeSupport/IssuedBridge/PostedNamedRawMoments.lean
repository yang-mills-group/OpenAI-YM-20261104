import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedPositionPrefixSmearing
import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedScreenedReports
import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedOriginalGroundGraph
import YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6OfficialGraphRead
import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.GraphCoefficients
noncomputable section
namespace IssuedBridge.PostedNamedRawMoments
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


local notation "GC" => _root_.IssuedMaxwell.GraphCoefficients.issued g
local notation "M₀" => WilsonCapturedPhysicalMSDatum.original g.core
local notation "μ₀" => Teller.logNu 1
open PostedScreenedReparametrization (screened)

theorem cofiled (n d k : ℕ) (x : Stage n) (u : Fin n → (maxwellReference g).sector d) :
    (GC).correlation n k (fun i => ⟨d, u i⟩) x.val = Equator.wave μ₀ M₀ d n x k u :=
  (WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6OfficialGraphRead.original
    g (c:=d) (fun i => ⟨d, u i⟩) (fun _ => le_rfl) x k).symm

theorem integrable (d k r n : ℕ) (A : Fin (r+1) → YangMills.MSbar.Position.EndAt (maxwellReference g) d)
    (φ : YangMills.SeparatedTest n) (v : Fin n → (maxwellReference g).sector d) :
    Integrable (fun x => φ x * YangMills.MSbar.Position.momentThrough GC d k r A n v x) :=
  PostedPositionPrefixSmearing.original M₀ μ₀ GC (cofiled (g:=g)) d k r n A φ v

theorem tree (n d : ℕ) (v : Fin n → (maxwellReference g).sector d) (x : Stage n) :
    (GC).correlation n 0 (fun i => ⟨d,v i⟩) x.val = (maxwellReference g).moment x.val (fun i => (v i).val) := by
  rw [cofiled n d 0 x v]
  exact PostedOriginalGroundGraph.original M₀ μ₀ (h:=d) (fun _ => d) (fun _ => le_rfl) v x

theorem measured (n d k : ℕ) (v : Fin n → (maxwellReference g).sector d) (x : Stage n) :
    YangMills.MSbar.Position.momentThrough GC d k k (fun j => screened Z M₀ μ₀ d j.val) n v x.val =
    Reg.State.wall μ₀ Z.store M₀ d x.val k v := by
  rw [PostedScreenedReports.opened Z M₀ μ₀ n d k x v]
  unfold YangMills.MSbar.Position.momentThrough
  apply Finset.sum_congr rfl
  intro ν _
  dsimp only
  split_ifs
  · exact cofiled n d _ x _
  · rfl

theorem original (d k n : ℕ) (φ : YangMills.SeparatedTest n) (v : Fin n → (maxwellReference g).sector d) :
    (∫ x : YangMills.Points n, φ x *
      YangMills.MSbar.Position.momentThrough GC d k k (fun j => screened Z M₀ μ₀ d j.val) n v x) =
    Reg.State.author μ₀ Z.store M₀ d k n φ v := by
  rw [Reg.State.exact_trace]
  apply YM.Test.apply_eq
  intro x hx
  exact measured Z n d k v ⟨x,hx⟩

end IssuedBridge.PostedNamedRawMoments
end
