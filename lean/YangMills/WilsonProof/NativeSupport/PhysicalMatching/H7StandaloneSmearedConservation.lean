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
namespace PhysicalMatching.H7StandaloneSmearedConservation
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
open YangMills.WilsonFamily MeasureTheory

private def origin {n : ℕ} (o : YangMills.Spacetime) : YangMills.Points n := WithLp.toLp 2 fun _ => o

theorem chartDerivative {n : ℕ} (r : ℝ) (o : YangMills.Spacetime) (x : YangMills.Points n) :
    HasFDerivAt (sites r o) (r • ContinuousLinearMap.id ℝ (YangMills.Points n)) x := by
  exact (r • ContinuousLinearMap.id ℝ (YangMills.Points n)).hasFDerivAt.const_add (origin o)

theorem physicalSmooth (V : Vision E ξ) (s : Option (wardHierarchy V).Character) {n : ℕ}
    (q : Fin n → (wardHierarchy V).Tag) (x : YangMills.Points n) (hx : x ∈ YM.conf n) :
    ContDiffAt ℝ ∞ ((wardHierarchy V).correlation s q) x :=
  (V.pupil.S.class_smooth (spectator V.pupil.last s) (spectate V.pupil.last s).smooth q x hx).contDiffAt
    ((YM.conf_open n).mem_nhds hx)

theorem shapedSmooth (V : Vision E ξ) (s : Option (wardHierarchy V).Character) {n : ℕ}
    (q : Fin n → (wardHierarchy V).Tag) (r : ℝ) (hr : 0 < r) (o : YangMills.Spacetime)
    (x : YangMills.Points n) (hx : x ∈ YM.conf n) :
    ContDiffAt ℝ ∞ (fun y => (wardHierarchy V).correlation s q (sites r o y)) x := by
  have h : ContDiff ℝ ∞ (sites r o : YangMills.Points n → YangMills.Points n) :=
    (contDiff_const (c := origin o)).add (r • ContinuousLinearMap.id ℝ (YangMills.Points n)).contDiff
  exact (physicalSmooth V s q (sites r o x) (YM.Answer.ContinuumLimit.ElectedMeasurement.centerSeparated hr o x hx)).comp x h.contDiffAt

set_option synthInstance.maxHeartbeats 240000 in
theorem derivativeAtShape (V : Vision E ξ) (s : Option (wardHierarchy V).Character) {n : ℕ}
    (q : Fin (n+1) → (wardHierarchy V).Tag) (r : ℝ) (hr : 0 < r) (o : YangMills.Spacetime)
    (x : YangMills.Points (n+1)) (hx : x ∈ YM.conf (n+1)) (a : YM.Axis) :
    YangMills.Ward.firstDerivative a (fun y => (wardHierarchy V).correlation s q (sites r o y)) x =
      (r : ℂ) * YangMills.Ward.firstDerivative a ((wardHierarchy V).correlation s q) (sites r o x) := by
  let F := (wardHierarchy V).correlation s q
  letI : ContinuousSMul ℝ (YangMills.Points (n+1)) :=
    inferInstanceAs (ContinuousSMul ℝ (PiLp 2 fun _ : Fin (n+1) => EuclideanSpace ℝ YM.Axis))
  have h := (physicalSmooth V s q (sites r o x) (YM.Answer.ContinuumLimit.ElectedMeasurement.centerSeparated hr o x hx)).differentiableAt (by simp)
  unfold YangMills.Ward.firstDerivative
  change (fderiv ℝ (F ∘ sites r o) x) _ = (r : ℂ) * (fderiv ℝ F (sites r o x)) _
  rw [(h.hasFDerivAt.comp x (chartDerivative r o x)).fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
    map_smul, Complex.real_smul]
  rfl

private theorem supportedProduct {n : ℕ} {f g : YangMills.Points n → ℂ}
    (hf : HasCompactSupport f) (hc : Continuous f) (hg : ∀ x ∈ tsupport f, ContinuousAt g x) :
    Integrable (fun x => f x * g x) := by
  apply Continuous.integrable_of_hasCompactSupport _ hf.mul_right
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x ∈ tsupport f
  · exact hc.continuousAt.mul (hg x hx)
  · apply continuousAt_const.congr (show (fun _ : YangMills.Points n => (0 : ℂ)) =ᶠ[𝓝 x] (fun y => f y * g y) from ?_)
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
    simp [hy]

private theorem signedParts {n : ℕ} (φ : YangMills.WilsonFamily.SeparatedTest (n+1)) (a : YM.Axis)
    (f : YangMills.Points (n+1) → ℂ) (hs : ∀ x ∈ tsupport φ, ContDiffAt ℝ ∞ f x) :
    Integrable (fun x => φ x * YangMills.Ward.firstDerivative a f x) ∧
    (∫ x, YangMills.Ward.firstDerivative a (fun y => φ y) x * f x) =
      -(∫ x, φ x * YangMills.Ward.firstDerivative a f x) := by
  let e : YangMills.Points (n+1) := PiLp.single 2 0 (EuclideanSpace.single a 1)
  have hφ : ContDiff ℝ ∞ (fun x => φ x) := φ.contDiff
  have hD : ∀ x ∈ tsupport φ, ContinuousAt (fun y => fderiv ℝ f y e) x := fun x hx =>
    ((hs x hx).fderiv_right (m := ∞) (by simp)).continuousAt.clm_apply continuousAt_const
  have h₁ : Integrable (fun x => fderiv ℝ (fun y => φ y) x e * f x) :=
    supportedProduct (φ.hasCompactSupport.fderiv_apply ℝ e) ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)
      (fun x hx => (hs x (tsupport_fderiv_apply_subset ℝ e hx)).continuousAt)
  have h₂ : Integrable (fun x => φ x * fderiv ℝ f x e) := supportedProduct φ.hasCompactSupport φ.continuous hD
  have h₃ : Integrable (fun x => φ x * f x) := supportedProduct φ.hasCompactSupport φ.continuous (fun x hx => (hs x hx).continuousAt)
  have hb : (∫ x, φ x * fderiv ℝ f x e) = -(∫ x, fderiv ℝ (fun y => φ y) x e * f x) :=
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable h₁ h₂ h₃
      (fun x _ => hφ.differentiable (by simp) x) (fun x hx => (hs x hx).differentiableAt (by simp))
  refine ⟨h₂,?_⟩
  change (∫ x, fderiv ℝ (fun y => φ y) x e * f x) = -(∫ x, φ x * fderiv ℝ f x e)
  rw [hb,neg_neg]

theorem original (V : Vision E ξ) (Z : WilsonPrescription g.core) (s : Option (wardHierarchy V).Character)
    (r : ℝ) (hr : 0 < r) (o : YangMills.Spacetime) (P : Pupils) (row : Fin 2) :
    conservation V Z s r o P (fun a b => (r ^ 4 : ℂ) • (wardHierarchy V).stress a b) row = 0 := by
  unfold conservation
  apply Finset.sum_eq_zero
  intro j _
  let φ := P.conservation row j
  let q : Fin 1 → (wardHierarchy V).Tag := fun _ => probeTag V Z r j
  let f (a : YM.Axis) : YangMills.Points 2 → ℂ := marked V s r o ((r ^ 4 : ℂ) • (wardHierarchy V).stress a 0) q
  have hs (a : YM.Axis) x (hx : x ∈ tsupport φ) : ContDiffAt ℝ ∞ (f a) x :=
    shapedSmooth V s (Fin.cons ⟨4,(r^4 : ℂ) • (wardHierarchy V).stress a 0⟩ q) r hr o x (φ.tsupport_subset hx)
  have hb (a : YM.Axis) := signedParts φ a (f a) (hs a)
  change (∑ a : YM.Axis, ∫ x : YangMills.Points 2, YangMills.Ward.firstDerivative a (fun y => φ y) x * f a x) = 0
  simp_rw [fun a => (hb a).2, Finset.sum_neg_distrib]
  rw [← integral_finsetSum _ (fun a _ => (hb a).1)]
  have zeroSum (x : YangMills.Points 2) : (∑ a : YM.Axis, φ x * YangMills.Ward.firstDerivative a (f a) x) = 0 := by
    by_cases hx : x ∈ tsupport φ
    · have hz (a : YM.Axis) := derivativeAtShape V s (Fin.cons ⟨4,(r^4 : ℂ) • (wardHierarchy V).stress a 0⟩ q) r hr o x (φ.tsupport_subset hx) a
      rw [← Finset.mul_sum]
      simp_rw [show ∀ a, YangMills.Ward.firstDerivative a (f a) x = _ from hz, ← Finset.mul_sum]
      rw [separatedConservation V s q (sites r o x) (YM.Answer.ContinuumLimit.ElectedMeasurement.centerSeparated hr o x (φ.tsupport_subset hx)) (r^4 : ℂ) 0]
      simp
    · have he : φ x = 0 := by
        by_contra hn
        exact hx (subset_tsupport _ (show x ∈ Function.support (fun y => φ y) from hn))
      simp [he]
  simp_rw [zeroSum]
  simp

end PhysicalMatching.H7StandaloneSmearedConservation

