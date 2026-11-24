import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedNamedRawMoments
import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.ElectedPrescription
import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.CalibratedStore
noncomputable section
namespace IssuedBridge.PostedNamedScreenBalance
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


variable (h : g.IsSimple)
local notation "P₀" => Subtype.val (_root_.IssuedMaxwell.ElectedPrescription.prior g h)
local notation "H₀" => Subtype.property (_root_.IssuedMaxwell.ElectedPrescription.prior g h)
local notation "Z₀" => _root_.IssuedMaxwell.ElectedPrescription.issued g h

theorem original (d k : ℕ) :
    ((P₀).screen d).read (fun n φ v => ∫ x : YangMills.Points n, φ x *
      YangMills.MSbar.Position.momentThrough GC d k k (fun j => screened Z₀ M₀ μ₀ d j.val) n v x) =
    if k = 0 then ((P₀).screen d).read (YangMills.MSbar.Position.free (maxwellReference g) d) else 0 := by
  simp_rw [PostedNamedRawMoments.original Z₀]
  let Q := Reg.State.author μ₀ (Z₀).store M₀ d k
  change ((P₀).screen d).read (_root_.IssuedMaxwell.Reports.printed Q) = _
  have book := (_root_.IssuedMaxwell.ElectedPrescription.original g h).2.1
  have readLaw (S : Normalize.Prediction g.core d) : (((Z₀).store.measure d).D S).val =
      ((P₀).screen d).read (_root_.IssuedMaxwell.Reports.printed S) := by
    rw [book]
    exact _root_.IssuedMaxwell.PositionStore.reported P₀ H₀ d S
  have balance := PostedScreenedReports.normalized Z₀ M₀ μ₀ d k
  by_cases hk : k = 0
  · rw [if_pos hk] at balance ⊢
    exact (readLaw Q).symm.trans ((congrArg Subtype.val balance).trans (readLaw (Normalize.reference g.core d)))
  · rw [if_neg hk] at balance ⊢
    exact (readLaw Q).symm.trans (congrArg Subtype.val balance)

end IssuedBridge.PostedNamedScreenBalance
end
