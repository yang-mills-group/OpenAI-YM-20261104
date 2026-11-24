import YangMills.WilsonProof.NativeSupport.IssuedBridge.PostedAppointedTriangleMoments
noncomputable section
namespace IssuedBridge.PostedAppointedFirstResponse
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

open Trace Graph3 Photo Cirrus Retirement Structure1 AxesTangent Lattice Finset PowerSeries
variable {n : ℕ}
private def sole : Option (Fin n)→Days n := fun i=> Finsupp.single i 1
private lemma toll1 : Injective (sole (n:=n)):=by intro i j he; by_contra! h; have hh:0=(1:ℕ):= (Finsupp.single_eq_of_ne h).symm.trans (show sole (n:=n) j i=1 by rw [← he]; exact Finsupp.single_eq_same); omega
private lemma totals : Normalize.tally 1 n= Finset.univ.image sole:=by
  ext1 v; rw [totaled,Finset.mem_image]; refine ⟨fun h=>?_,?_⟩; swap; · rintro ⟨i,_,rfl⟩; simp [sole]
  have he: Pages.Volume v=1:=by rw [Pages.Volume,Finsupp.weight,LinearMap.toAddMonoidHom_coe, Finsupp.linearCombination_apply,Finsupp.sum_of_support_subset v (Finset.subset_univ _) _ (by simp)]; simpa using h
  obtain ⟨i,rfl⟩:= Chiral.rank1_support v he; exact ⟨i,Finset.mem_univ _,rfl⟩

theorem response (E : Guard g.core 6) (P : ℕ → Structure1.Point g.core 6 3)
    (he : PowerSeries.constantCoeff E = 1) :
    Dframe.status E P 1 = P 1 + lot (P 0) (PowerSeries.coeff 1 E) := by
  ext1 v
  rw [Dframe.seen, _root_.add_apply, lots, totals, Finset.sum_image toll1.injOn, Fintype.sum_option]
  have head : pulseU (sole (n:=3) none) E v = v := by
    funext i
    simp only [pulseU, sole, Finsupp.single_eq_of_ne (Option.some_ne_none i),
      PowerSeries.coeff_zero_eq_constantCoeff_apply, he]
    rfl
  rw [head, show sole (n:=3) none none = 1 from Finsupp.single_eq_same]
  apply congrArg (_ + ·)
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show sole (some i) = jumpDay 3 1 i from rfl, Normalize.drift, jumpDay,
      Finsupp.single_eq_of_ne (Option.some_ne_none _).symm,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, he]
  rfl

theorem bare (x : Stage 3) :
    (P₀).triangle.firstConnected GC x.val =
    PowerSeries.coeff 1 (Rose.b3 (Rose.batchT (Dframe.meteor μ₀ M₀ 6 x.val))) := by
  rw [YangMills.MSbar.Position.Triangle.firstConnected, PostedAppointedTriangleMoments.cumulant]
  apply congrArg (fun m => PowerSeries.coeff 1 (Rose.b3 m))
  funext I
  apply PowerSeries.ext
  intro j
  simp only [Rose.batchT, PowerSeries.coeff_mk]
  rw [← PostedAppointedTriangleFaces.original g h I]
  exact PostedNamedRawMoments.cofiled 3 6 j x _
end IssuedBridge.PostedAppointedFirstResponse
end
