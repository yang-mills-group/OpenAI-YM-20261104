import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedAppointedTriangleMoments
noncomputable section
namespace IssuedBridge.PostedAppointedTriangleIntegrability
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

private def coefficientContinuous (F : YM.Points 3 → PowerSeries ℂ) : Prop :=
  ∀ k, ContinuousOn (fun x => PowerSeries.coeff k (F x)) (YM.conf 3)

private theorem sumContinuous {F H : YM.Points 3 → PowerSeries ℂ}
    (f : coefficientContinuous F) (h : coefficientContinuous H) :
    coefficientContinuous (fun x => F x + H x) := by
  intro k
  apply ((f k).add (h k)).congr
  intro x _
  simp only [map_add, Pi.add_apply]

private theorem differenceContinuous {F H : YM.Points 3 → PowerSeries ℂ}
    (f : coefficientContinuous F) (h : coefficientContinuous H) :
    coefficientContinuous (fun x => F x - H x) := by
  intro k
  apply ((f k).sub (h k)).congr
  intro x _
  simp only [map_sub, Pi.sub_apply]

private theorem productContinuous {F H : YM.Points 3 → PowerSeries ℂ}
    (f : coefficientContinuous F) (h : coefficientContinuous H) :
    coefficientContinuous (fun x => F x * H x) := by
  intro k
  simp only [PowerSeries.coeff_mul]
  exact continuousOn_finsetSum _ fun i _ => (f i.1).mul (h i.2)

theorem trace (k : ℕ) : ContinuousOn
    (fun x : YM.Points 3 => PowerSeries.coeff k (Reg.Choice.trace μ₀ M₀ (Z₀).store x))
    (YM.conf 3) := by
  let F := fun (I : Finset (Fin 3)) (x : YM.Points 3) =>
    Rose.batchT (Reg.State.wall μ₀ (Z₀).store M₀ 6 x) I
  have cf (I : Finset (Fin 3)) : coefficientContinuous (F I) := by
    intro j
    simp only [F, Rose.batchT, PowerSeries.coeff_mk]
    exact Reg.State.road μ₀ (Z₀).store M₀ _ j
  have pairs := sumContinuous
    (sumContinuous (productContinuous (cf {0,1}) (cf {2}))
      (productContinuous (cf {0,2}) (cf {1})))
    (productContinuous (cf {1,2}) (cf {0}))
  have triple := productContinuous (productContinuous (cf {0}) (cf {1})) (cf {2})
  simpa only [Reg.Choice.trace, Rose.b3, two_smul, F] using
    (sumContinuous (differenceContinuous (cf Finset.univ) pairs) (sumContinuous triple triple) k)

theorem original (k : ℕ) : Integrable
    (fun x => (P₀).triangle.profile x * YangMills.MSbar.Position.triangleKernel GC P₀ k x) := by
  apply YM.Test.smearing
  apply (trace h k).congr
  intro x hx
  exact PostedAppointedTriangleMoments.kernel h k ⟨x, hx⟩
end IssuedBridge.PostedAppointedTriangleIntegrability
end
