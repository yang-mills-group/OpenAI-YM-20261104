import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7StandaloneAppointedWardBalance
import YM.Integration.WilsonGraphAppointedPublicMeasurement
import YM.Integration.WilsonGraphMeasuredCompactCorrelation
import YangMills.WilsonProof.NativeSupport.WardBridge
import YangMills.WilsonProof.NativeSupport.MaxwellBridge
import YM.XSpace.Twins
import YangMills.WilsonProof.NativeSupport.YM.Next.MAXWELL.Stress

set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
namespace PhysicalMatching.H7StandaloneTranslationTestSupport
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

open PhysicalMatching.H7StandaloneAppointedPublicWardRows
open PhysicalMatching.H7StandaloneFourSmearedWardReadings
open PhysicalMatching.H7StandaloneAppointedWardBalance

def weight (P : Pupils) (a : YM.Axis) (u : YangMills.Spacetime × YangMills.Points 2) : ℂ :=
  P.translation u.2 * Complex.ofReal (YangMills.Maxwell.partialD a P.cutoff u.1)

theorem germ {χ : YangMills.Spacetime → ℝ} {x : YangMills.Spacetime} {k : ℝ}
    (hc : χ =ᶠ[𝓝 x] (fun _ => k)) (a : YM.Axis) :
    x ∉ tsupport (YangMills.Maxwell.partialD a χ) := by
  apply notMem_tsupport_iff_eventuallyEq.mpr
  filter_upwards [eventually_eventually_nhds.mpr hc] with z hz
  have hlocal : χ =ᶠ[𝓝 z] (fun _ : YangMills.Spacetime => k) := hz
  have hd : fderiv ℝ χ z = fderiv ℝ (fun _ : YangMills.Spacetime => k) z := hlocal.fderiv_eq
  change fderiv ℝ χ z (EuclideanSpace.single a 1) = 0
  simp [hd]

theorem shellAvoids {n : ℕ} {x : YangMills.Points (n+1)} {χ : YangMills.Spacetime → ℝ}
    (hw : YangMills.Ward.Window x χ) (a : YM.Axis) {z : YangMills.Spacetime}
    (hz : z ∈ tsupport (YangMills.Maxwell.partialD a χ)) : ∀ i, z ≠ x i := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · rintro rfl
    exact germ hw.2.2.1 a hz
  · rintro rfl
    exact hw.2.2.2 j (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single a 1) hz)

theorem supported (P : Pupils) (a : YM.Axis) :
    tsupport (weight P a) ⊆
      (tsupport (YangMills.Maxwell.partialD a P.cutoff)) ×ˢ (tsupport (fun x => P.translation x)) := by
  apply closure_minimal _ (isClosed_tsupport _ |>.prod (isClosed_tsupport _))
  intro u hu
  have hn : P.translation u.2 ≠ 0 ∧ YangMills.Maxwell.partialD a P.cutoff u.1 ≠ 0 := by
    constructor
    · intro h
      exact hu (by simp [weight,h])
    · intro h
      exact hu (by simp [weight,h])
  exact ⟨subset_tsupport _ hn.2,subset_tsupport _ hn.1⟩

theorem compact (P : Pupils) (a : YM.Axis) : HasCompactSupport (weight P a) := by
  by_cases he : (tsupport (fun x => P.translation x)).Nonempty
  · obtain ⟨x,hx⟩ := he
    have hχ := (P.window x hx).2.1.fderiv_apply ℝ (EuclideanSpace.single a 1)
    exact (hχ.prod P.translation.hasCompactSupport).of_isClosed_subset (isClosed_tsupport _) (supported P a)
  · have hφ : tsupport (fun x => P.translation x) = ∅ := Set.not_nonempty_iff_eq_empty.mp he
    apply isCompact_empty.of_isClosed_subset (isClosed_tsupport _)
    simpa [hφ] using supported P a

theorem smoothWeight (P : Pupils) (a : YM.Axis) : Continuous (weight P a) := by
  by_cases he : (tsupport (fun x => P.translation x)).Nonempty
  · obtain ⟨x,hx⟩ := he
    have hχ := (P.window x hx).1
    have hD : Continuous (YangMills.Maxwell.partialD a P.cutoff) :=
      (hχ.continuous_fderiv (by simp)).clm_apply continuous_const
    exact (P.translation.continuous.comp continuous_snd).mul (Complex.continuous_ofReal.comp (hD.comp continuous_fst))
  · have hφ : ∀ x, P.translation x = 0 := by
      intro x
      by_contra hx
      exact he ⟨x,subset_tsupport _ hx⟩
    have hz : weight P a = fun _ => (0 : ℂ) := by
      funext u
      simp only [weight, hφ u.2, zero_mul]
    rw [hz]
    exact continuous_const

theorem separated (P : Pupils) (a : YM.Axis) {u : YangMills.Spacetime × YangMills.Points 2}
    (hu : u ∈ tsupport (weight P a)) : YangMills.Ward.prepend u.1 u.2 ∈ YM.conf 3 := by
  obtain ⟨hz,hx⟩ := supported P a hu
  exact YM.Work.A01.conf_cons (P.translation.tsupport_subset hx) (shellAvoids (P.window u.2 hx) a hz)

theorem original (P : Pupils) (a : YM.Axis) (f : YangMills.Spacetime × YangMills.Points 2 → ℂ)
    (hf : ∀ u, YangMills.Ward.prepend u.1 u.2 ∈ YM.conf 3 → ContinuousAt f u) :
    Integrable (fun u => weight P a u * f u) := by
  have hc : Continuous (fun u => weight P a u * f u) := by
    rw [continuous_iff_continuousAt]
    intro u
    by_cases hu : u ∈ tsupport (weight P a)
    · exact (smoothWeight P a).continuousAt.mul (hf u (separated P a hu))
    · have he := notMem_tsupport_iff_eventuallyEq.mp hu
      have hz : ContinuousAt (fun _ : YangMills.Spacetime × YangMills.Points 2 => (0 : ℂ)) u := continuousAt_const
      apply hz.congr_of_eventuallyEq
      filter_upwards [he] with y hy
      change weight P a y * f y = 0
      rw [show weight P a y = 0 from hy, zero_mul]
  exact hc.integrable_of_hasCompactSupport (show HasCompactSupport (weight P a * f) from (compact P a).mul_right)

end PhysicalMatching.H7StandaloneTranslationTestSupport

