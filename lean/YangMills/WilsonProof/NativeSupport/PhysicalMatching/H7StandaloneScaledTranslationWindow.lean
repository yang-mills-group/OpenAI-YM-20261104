import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7StandaloneFourSmearedWardReadings
import YM.Integration.WilsonGraphAppointedPublicMeasurement
import YM.Integration.WilsonGraphMeasuredCompactCorrelation
import YangMills.WilsonProof.NativeSupport.WardBridge
import YangMills.WilsonProof.NativeSupport.MaxwellBridge
import YM.XSpace.Twins
import YangMills.WilsonProof.NativeSupport.YM.Next.MAXWELL.Stress

set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
namespace PhysicalMatching.H7StandaloneScaledTranslationWindow
open YM YM.Answer YM.Answer.ContinuumLimit


open Lattice RG MeasureTheory Function Filter Wilson Integration Integration.Election Climb Extraction Trace.Pilot
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato FullVolume Spec Table Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Structure1
open MS MS.High MS.Native MS.Land MS.Fleet MS.Tide MS.Book PhysMS PhysMS.Frame Next.UVStress Order Spin OPE OPE.Orbits
open FVA2 FVA2.Register FVA2.Scale.Level FVA2.Scale SignedWilsonExpansion SignedWilsonExpansion.Belle SignedWilsonExpansion.Belle.Path SignedWilsonExpansion.Museum SignedWilsonExpansion.Kane SignedWilsonExpansion.Kane.Tilted SignedWilsonExpansion.Camera
open Asymptotics WilsonPositionHomogeneousComparison
open PowerSeries XSpace.Cirrus Entree Future
open Integration Integration.Election Extraction Climb Lattice Wilson RG Function Filter Trace.Pilot
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Table Spec
open PhysMS PhysMS.Frame Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Structure1 FVA2 FVA2.Register Scale OPE OPE.Orbits
open SignedWilsonExpansion SignedWilsonExpansion.Kane SignedWilsonExpansion.StageG Camera SignedWilsonExpansion.Kane.Tilted Next.UVStress XSpace.Cirrus
open MS MS.High MS.Land MS.Native MS.Tide MS.Fleet MS.Book PowerSeries Asymptotics
open Belfry Belle Dancer Belfry.ScaleFits Belfry.Classroom Scale Level GroupS
open scoped BigOperators Classical ContDiff Topology

open YangMills
open _root_.IssuedBridge
open YangMills
open YM YM.Integration YM.Spec YM.OPE YM.OPE.Orbits YM.Maxwell YM.Maxwell.Free
open WilsonOneFrameMixedMaxwell WilsonPositionHomogeneousFrame
open Climb Lattice RG PhysMS Trace.Pilot Next.Extract PhysicalNext.Repeat.Legato RG17 XSpace XSpace.Normalize FVA2 FVA2.Register
open FixedFields
open Function Filter Set
open scoped Topology BigOperators Classical
open MS MS.Land MS.Fleet FVA2.Scale WilsonViewerReportingGrid WilsonThermometerWeakMeasuredSeries
open WilsonViewerGridPins WilsonViewerAlignedResidual WilsonViewerElectedHierarchy
open WilsonPositionThermometerCapStation WilsonPositionCapTransport WilsonLimitConstruction
open YM.FVA2.Scale YM.MS YM.MS.Fleet YM.MS.Land YangMills.Matching
open YangMills.Matching
universe u
variable {g : YangMills.GaugeGroup} {R : Run g.core}
variable {H : g.core.Simple} {ε : ℝ} {e : YM.Axis} {O : OrderS g.core}
variable {E : Construction.{u} H ε e O} {ξ : Extraction.Order}



open YM.Maxwell.Free YM.Maxwell.Wick YM.XSpace.Normalize
open scoped BigOperators Classical

open PhysicalMatching.H7StandaloneFourSmearedWardReadings
open PhysicalMatching.H7StandaloneAppointedPublicWardRows
open scoped Topology
def shellChart (r : ℝ) (hr : 0 < r) (o : YangMills.Spacetime) :
    YangMills.Spacetime ≃ₜ YangMills.Spacetime where
  toFun z := o + r • z
  invFun y := r⁻¹ • (y - o)
  left_inv z := by
    change r⁻¹ • ((o + r • z) - o) = z
    rw [add_sub_cancel_left,inv_smul_smul₀ hr.ne']
  right_inv y := by
    change o + r • (r⁻¹ • (y-o)) = y
    rw [smul_inv_smul₀ hr.ne']
    abel
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def transported (r : ℝ) (hr : 0 < r) (o : YangMills.Spacetime)
    (χ : YangMills.Spacetime → ℝ) := χ ∘ (shellChart r hr o).symm

theorem window {n : ℕ} (r : ℝ) (hr : 0 < r) (o : YangMills.Spacetime)
    (x : YangMills.Points (n+1)) {χ : YangMills.Spacetime → ℝ} (hw : YangMills.Ward.Window x χ) :
    YangMills.Ward.Window (sites r o x) (transported r hr o χ) := by
  let h := shellChart r hr o
  have hc (i : Fin (n+1)) : Tendsto h.symm (𝓝 (sites r o x i)) (𝓝 (x i)) := by
    change Tendsto h.symm (𝓝 (h (x i))) (𝓝 (x i))
    have hh : Tendsto h.symm (𝓝 (h (x i))) (𝓝 (h.symm (h (x i)))) := h.symm.continuous.continuousAt
    simpa only [h.symm_apply_apply] using hh
  have hs : ContDiff ℝ ∞ h.symm := by
    change ContDiff ℝ ∞ (fun y : YangMills.Spacetime => r⁻¹ • (y-o))
    fun_prop
  refine ⟨hw.1.comp hs,hw.2.1.comp_homeomorph h.symm,hw.2.2.1.comp_tendsto (hc 0),?_⟩
  intro i
  apply notMem_tsupport_iff_eventuallyEq.mpr
  exact (notMem_tsupport_iff_eventuallyEq.mp (hw.2.2.2 i)).comp_tendsto (hc i.succ)

theorem cutoffDerivative (r : ℝ) (hr : 0 < r) (o : YangMills.Spacetime)
    (χ : YangMills.Spacetime → ℝ) (hχ : ContDiff ℝ ∞ χ) (a : YM.Axis) (z : YangMills.Spacetime) :
    YangMills.Maxwell.partialD a (transported r hr o χ) (o+r • z) =
      r⁻¹ * YangMills.Maxwell.partialD a χ z := by
  let h := shellChart r hr o
  have hi : HasFDerivAt h.symm (r⁻¹ • ContinuousLinearMap.id ℝ YangMills.Spacetime) (h z) := by
    change HasFDerivAt (fun y : YangMills.Spacetime => r⁻¹ • (y-o)) _ _
    convert ((hasFDerivAt_id (h z)).sub_const o).const_smul r⁻¹ using 1 <;> first | rfl | ext y i <;> rfl
  have hf := ((hχ.differentiable (by simp)).differentiableAt (x := h.symm (h z))).hasFDerivAt
  change fderiv ℝ (χ ∘ h.symm) (h z) (EuclideanSpace.single a 1) = _
  rw [(hf.comp _ hi).fderiv, h.symm_apply_apply]
  simp [YangMills.Maxwell.partialD,ContinuousLinearMap.comp_apply,smul_eq_mul]

theorem affineVolume (r : ℝ) (hr : 0 < r) (o : YangMills.Spacetime) (f : YangMills.Spacetime → ℂ) :
    (∫ y, f y) = r^4 • ∫ z : YangMills.Spacetime, f (o+r • z) := by
  calc
    _ = ∫ z, f (o+z) := (integral_add_left_eq_self f o).symm
    _ = _ := by
      rw [show (fun z => f (o+r • z)) = (fun z => (fun y => f (o+y)) (r • z)) from rfl]
      rw [MeasureTheory.Measure.integral_comp_smul_of_nonneg volume (fun y => f (o+y)) r (hR := hr.le)]
      rw [show Module.finrank ℝ YangMills.Spacetime = 4 by simp,
        smul_inv_smul₀ (by positivity : r^4 ≠ 0)]

theorem prependSites {n : ℕ} (r : ℝ) (o z : YangMills.Spacetime) (x : YangMills.Points n) :
    YangMills.Ward.prepend (o+r • z) (sites r o x) = sites r o (YangMills.Ward.prepend z x) := by
  ext1 i
  refine Fin.cases ?_ (fun k => ?_) i <;> rfl

theorem original (V : Vision E ξ) (s : Option (wardHierarchy V).Character) {n d : ℕ}
    (r : ℝ) (hr : 0 < r) (o : YangMills.Spacetime) (x : YangMills.Points (n+1))
    (v : (wardHierarchy V).Field d) (q : Fin n → (wardHierarchy V).Tag)
    {χ : YangMills.Spacetime → ℝ} (hw : YangMills.Ward.Window x χ) (b : YM.Axis) :
    (wardHierarchy V).translationFlux s (sites r o x) v q (transported r hr o χ) b =
      -(∑ a : YM.Axis, r^4 • ∫ z : YangMills.Spacetime,
        ((r⁻¹ * YangMills.Maxwell.partialD a χ z : ℝ) : ℂ) *
          (wardHierarchy V).correlation s
            (Fin.cons ⟨4,(wardHierarchy V).stress a b⟩ (Fin.cons ⟨d,v⟩ q))
            (sites r o (YangMills.Ward.prepend z x))) := by
  unfold YangMills.Hierarchy.translationFlux
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [affineVolume r hr o]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with z
  rw [cutoffDerivative r hr o χ hw.1 a z]
  simp only [YangMills.Hierarchy.shellCorrelation,prependSites]

end PhysicalMatching.H7StandaloneScaledTranslationWindow

