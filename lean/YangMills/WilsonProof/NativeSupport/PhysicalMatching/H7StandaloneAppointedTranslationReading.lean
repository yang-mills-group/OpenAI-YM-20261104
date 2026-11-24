import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7StandaloneSmearedConservation
import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7StandaloneScaledTranslationWindow
import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7StandaloneTranslationTestSupport
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
namespace PhysicalMatching.H7StandaloneAppointedTranslationReading
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

open MeasureTheory
open PhysicalMatching.H7StandaloneAppointedPublicWardRows PhysicalMatching.H7StandaloneFourSmearedWardReadings
open PhysicalMatching.H7StandaloneAppointedWardBalance
open PhysicalMatching.H7StandaloneSmearedConservation
open scoped BigOperators Classical Topology

def prependLinear : (YangMills.Spacetime × YangMills.Points 2) →ₗ[ℝ] YangMills.Points 3 where
  toFun u := YangMills.Ward.prepend u.1 u.2
  map_add' u v := by ext1 i; refine Fin.cases ?_ (fun k => ?_) i <;> rfl
  map_smul' t u := by ext1 i; refine Fin.cases ?_ (fun k => ?_) i <;> rfl

private theorem continuousPrepend : Continuous (fun z : YangMills.Spacetime × YangMills.Points 2 => YangMills.Ward.prepend z.1 z.2) := by
  unfold YangMills.Ward.prepend
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => YangMills.Spacetime)).comp
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact continuous_fst
  · exact (PiLp.continuous_apply 2 (fun _ : Fin 2 => YangMills.Spacetime) j).comp continuous_snd

def density (V : Vision E ξ) (Z : WilsonPrescription g.core) (s : Option (wardHierarchy V).Character)
    (r : ℝ) (o : YangMills.Spacetime) (P : Pupils) (a : YM.Axis)
    (z : YangMills.Spacetime) (x : YangMills.Points 2) : ℂ :=
  ((YangMills.Maxwell.partialD a P.cutoff z : ℝ) : ℂ) *
    marked V s r o ((r^4 : ℂ) • (wardHierarchy V).stress a 0) (fun _ : Fin 2 => probeTag V Z r 0)
      (YangMills.Ward.prepend z x)

theorem atShell (V : Vision E ξ) (Z : WilsonPrescription g.core) (s : Option (wardHierarchy V).Character)
    (r : ℝ) (hr : 0 < r) (o : YangMills.Spacetime) (P : Pupils)
    (x : YangMills.Points 2) (hx : x ∈ tsupport (fun y => P.translation y)) :
    -(∑ a : YM.Axis, ∫ z, density V Z s r o P a z x) =
      YangMills.Ward.firstDerivative 0 (fun y =>
        (wardHierarchy V).correlation s (fun _ : Fin 2 => probeTag V Z r 0) (sites r o y)) x := by
  let v := YM.Answer.ContinuumLimit.ElectedMeasurement.frame V Z r 4 (probes H 0)
  let q : Fin 1 → (wardHierarchy V).Tag := fun _ => probeTag V Z r 0
  have hq : Fin.cons (α := fun _ : Fin 2 => (wardHierarchy V).Tag) ⟨4,v⟩ q =
      (fun _ : Fin 2 => probeTag V Z r 0) := by
    funext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  let χ := PhysicalMatching.H7StandaloneScaledTranslationWindow.transported r hr o P.cutoff
  have hw := PhysicalMatching.H7StandaloneScaledTranslationWindow.window r hr o x (P.window x hx)
  have h := PhysicalMatching.H7StandaloneScaledTranslationWindow.original V s r hr o x v q (P.window x hx) 0
  have hxr := YM.Answer.ContinuumLimit.ElectedMeasurement.centerSeparated hr o x (P.translation.tsupport_subset hx)
  calc
    _ = (r : ℂ) * (wardHierarchy V).translationFlux s (sites r o x) v q χ 0 := by
      rw [show (wardHierarchy V).translationFlux s (sites r o x) v q χ 0 = _ from h,
        mul_neg, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro a _
      rw [Complex.real_smul, ← mul_assoc, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with z
      unfold density marked
      rw [hq, firstSlot_eq, firstSlot_eq, map_smul]
      simp only [smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_pow]
      field_simp [hr.ne']
    _ = _ := by
      rw [(PhysicalMatching.H7StandaloneAppointedPublicWardRows.original V).translation s (sites r o x) hxr v q χ hw 0, hq]
      exact (derivativeAtShape V s (fun _ : Fin 2 => probeTag V Z r 0) r hr o x (P.translation.tsupport_subset hx) 0).symm

theorem integrable (V : Vision E ξ) (Z : WilsonPrescription g.core) (s : Option (wardHierarchy V).Character)
    (r : ℝ) (hr : 0 < r) (o : YangMills.Spacetime) (P : Pupils) (a : YM.Axis) :
    Integrable (fun u : YangMills.Spacetime × YangMills.Points 2 =>
      P.translation u.2 * density V Z s r o P a u.1 u.2) := by
  let q := Fin.cons (α := fun _ : Fin 3 => (wardHierarchy V).Tag)
      ⟨4,(r^4 : ℂ) • (wardHierarchy V).stress a 0⟩ (fun _ : Fin 2 => probeTag V Z r 0)
  let f (u : YangMills.Spacetime × YangMills.Points 2) :=
      (wardHierarchy V).correlation s q (sites r o (YangMills.Ward.prepend u.1 u.2))
  have h := PhysicalMatching.H7StandaloneTranslationTestSupport.original P a f (by
    intro u hu
    let m : YangMills.Spacetime × YangMills.Points 2 → YangMills.Points 3 := fun y => YangMills.Ward.prepend y.1 y.2
    have hs : ContinuousAt (fun y : YangMills.Points 3 => (wardHierarchy V).correlation s q (sites r o y)) (m u) :=
      (shapedSmooth V s q r hr o (m u) hu).continuousAt
    have hm : ContinuousAt m u := continuousPrepend.continuousAt
    exact hs.comp hm)
  simpa only [PhysicalMatching.H7StandaloneTranslationTestSupport.weight, density, marked, mul_assoc] using h

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
    (r : ℝ) (hr : 0 < r) (o : YangMills.Spacetime) (P : Pupils) :
    flux V Z s r o P (fun a b => (r^4 : ℂ) • (wardHierarchy V).stress a b) =
      -(∫ x : YangMills.Points 2, YangMills.Ward.firstDerivative 0 (fun y => P.translation y) x *
        (wardHierarchy V).correlation s (fun _ : Fin 2 => probeTag V Z r 0) (sites r o x)) := by
  let f (x : YangMills.Points 2) := (wardHierarchy V).correlation s (fun _ : Fin 2 => probeTag V Z r 0) (sites r o x)
  let w (a : YM.Axis) (u : YangMills.Spacetime × YangMills.Points 2) := P.translation u.2 * density V Z s r o P a u.1 u.2
  have hi (a : YM.Axis) : Integrable (w a) (volume.prod volume) := integrable V Z s r hr o P a
  have hφ := signedParts P.translation 0 f (fun x hx =>
    shapedSmooth V s (fun _ : Fin 2 => probeTag V Z r 0) r hr o x (P.translation.tsupport_subset hx))
  have inner (x : YangMills.Points 2) :
      -(∑ a : YM.Axis, ∫ z : YangMills.Spacetime, w a (z,x)) = P.translation x * YangMills.Ward.firstDerivative 0 f x := by
    by_cases hx : x ∈ tsupport (fun y => P.translation y)
    · simp_rw [w, integral_const_mul, ← Finset.mul_sum, ← mul_neg]
      exact congrArg (fun z => P.translation x * z) (atShell V Z s r hr o P x hx)
    · have he : P.translation x = 0 := by
        by_contra hn; exact hx (subset_tsupport _ hn)
      simp [w,he]
  calc
    _ = -(∑ a : YM.Axis, ∫ u : YangMills.Spacetime × YangMills.Points 2, w a u ∂(volume.prod volume)) := by
      simp only [flux,w,density,mul_assoc]
      rfl
    _ = ∫ x : YangMills.Points 2, -(∑ a : YM.Axis, ∫ z : YangMills.Spacetime, w a (z,x)) := by
      simp_rw [integral_prod_symm _ (hi _)]
      rw [integral_neg, integral_finsetSum _ (fun a _ => (hi a).integral_prod_right)]
    _ = ∫ x : YangMills.Points 2, P.translation x * YangMills.Ward.firstDerivative 0 f x := by simp_rw [inner]
    _ = _ := by rw [hφ.2,neg_neg]

