import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedNamedBlindResidual
import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedNamedScreenBalance
import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.ElectedPrescription
import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.CalibratedStore
noncomputable section
namespace IssuedBridge.PostedAppointedRawFrame
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

open YangMills.MSbar.Position (rawFrame framePrefix)
theorem step (d k : ℕ) :
    screened Z₀ M₀ μ₀ d (k+1) = -((P₀).screen d).read
      (YangMills.MSbar.Position.residualReport GC d k (fun j => screened Z₀ M₀ μ₀ d j.val)) := by
  rw [PostedNamedBlindResidual.correction]
  apply congrArg Neg.neg
  rw [(_root_.IssuedMaxwell.ElectedPrescription.original g h).2.1, _root_.IssuedMaxwell.PositionStore.reported]
  apply congrArg ((P₀).screen d).read
  funext n φ v
  exact (PostedNamedBlindResidual.original Z₀ d k n φ v).symm

theorem frameAgrees (d k : ℕ) : screened Z₀ M₀ μ₀ d k = rawFrame GC P₀ d k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero =>
      rw [PostedScreenedReports.ground, YangMills.MSbar.Position.rawFrame_zero]
      rfl
    | succ k =>
      rw [step, YangMills.MSbar.Position.rawFrame_succ]
      have old : (fun j : Fin (k+1) => screened Z₀ M₀ μ₀ d j.val) = framePrefix GC P₀ d k := by
        funext j
        exact (ih j.val j.isLt).trans (YangMills.MSbar.Position.framePrefix_coeff GC P₀ d k j).symm
      rw [old]

theorem through (d k : ℕ) : framePrefix GC P₀ d k = fun j => screened Z₀ M₀ μ₀ d j.val := by
  funext j
  exact (YangMills.MSbar.Position.framePrefix_coeff GC P₀ d k j).trans (frameAgrees h d j.val).symm

theorem original : YangMills.MSbar.Position.RawValid GC P₀ := by
  constructor
  · intro n d v x hx
    exact PostedNamedRawMoments.tree n d v ⟨x,hx⟩
  · intro d e k p q same
    rw [← frameAgrees h d k, ← frameAgrees h e k]
    exact PostedScreenedReports.nested Z₀ M₀ μ₀ d e k p q same
  · intro d k n φ v
    exact PostedNamedRawMoments.integrable d (k+1) k n _ φ v
  · intro d k n φ v
    exact PostedNamedRawMoments.integrable d k k n _ φ v
  · intro d k
    unfold YangMills.MSbar.Position.rawReport YangMills.MSbar.Position.rawMoment
    rw [through h d k]
    exact PostedNamedScreenBalance.original h d k
end IssuedBridge.PostedAppointedRawFrame
end
