import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7StandaloneVacuumWardReading
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
namespace PhysicalMatching.H7StandaloneArbitraryWardTestReadings
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

open YangMills.WilsonFamily
open PhysicalMatching.H7StandaloneVacuumWardReading

structure Shell (n : ℕ) where
  translation : YangMills.WilsonFamily.SeparatedTest (n+1)
  cutoff : YangMills.Spacetime → ℝ
  window : ∀ x ∈ tsupport (fun y => translation y), YangMills.Ward.Window x cutoff

def weight {n : ℕ} (P : Shell n) (a : YM.Axis) (u : YangMills.Spacetime × YangMills.Points (n+1)) : ℂ :=
  P.translation u.2 * Complex.ofReal (YangMills.Maxwell.partialD a P.cutoff u.1)

theorem supported {n : ℕ} (P : Shell n) (a : YM.Axis) :
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

theorem compact {n : ℕ} (P : Shell n) (a : YM.Axis) : HasCompactSupport (weight P a) := by
  by_cases he : (tsupport (fun x => P.translation x)).Nonempty
  · obtain ⟨x,hx⟩ := he
    have hχ := (P.window x hx).2.1.fderiv_apply ℝ (EuclideanSpace.single a 1)
    exact (hχ.prod P.translation.hasCompactSupport).of_isClosed_subset (isClosed_tsupport _) (supported P a)
  · have hφ : tsupport (fun x => P.translation x) = ∅ := Set.not_nonempty_iff_eq_empty.mp he
    apply isCompact_empty.of_isClosed_subset (isClosed_tsupport _)
    simpa [hφ] using supported P a

theorem smoothWeight {n : ℕ} (P : Shell n) (a : YM.Axis) : Continuous (weight P a) := by
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

theorem separated {n : ℕ} (P : Shell n) (a : YM.Axis) {u : YangMills.Spacetime × YangMills.Points (n+1)}
    (hu : u ∈ tsupport (weight P a)) : YangMills.Ward.prepend u.1 u.2 ∈ YM.conf ((n+1)+1) := by
  obtain ⟨hz,hx⟩ := supported P a hu
  exact YM.Work.A01.conf_cons (P.translation.tsupport_subset hx) (PhysicalMatching.H7StandaloneTranslationTestSupport.shellAvoids (P.window u.2 hx) a hz)

theorem shellIntegrable {n : ℕ} (P : Shell n) (a : YM.Axis) (f : YangMills.Spacetime × YangMills.Points (n+1) → ℂ)
    (hf : ∀ u, YangMills.Ward.prepend u.1 u.2 ∈ YM.conf ((n+1)+1) → ContinuousAt f u) :
    Integrable (fun u => weight P a u * f u) := by
  have hc : Continuous (fun u => weight P a u * f u) := by
    rw [continuous_iff_continuousAt]
    intro u
    by_cases hu : u ∈ tsupport (weight P a)
    · exact (smoothWeight P a).continuousAt.mul (hf u (separated P a hu))
    · have he := notMem_tsupport_iff_eventuallyEq.mp hu
      have hz : ContinuousAt (fun _ : YangMills.Spacetime × YangMills.Points (n+1) => (0 : ℂ)) u := continuousAt_const
      apply hz.congr_of_eventuallyEq
      filter_upwards [he] with y hy
      rw [show weight P a y = 0 from hy, zero_mul]
  exact hc.integrable_of_hasCompactSupport (show HasCompactSupport (weight P a * f) from (compact P a).mul_right)

def prependLinear (n : ℕ) : (YangMills.Spacetime × YangMills.Points (n+1)) →ₗ[ℝ] YangMills.Points ((n+1)+1) where
  toFun u := YangMills.Ward.prepend u.1 u.2
  map_add' u v := by ext1 i; refine Fin.cases ?_ (fun k => ?_) i <;> rfl
  map_smul' t u := by ext1 i; refine Fin.cases ?_ (fun k => ?_) i <;> rfl

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

theorem testParts {n : ℕ} (φ : YangMills.WilsonFamily.SeparatedTest (n+1)) (a : YM.Axis)
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


theorem vacuumTest (V : Vision E ξ) (s : Option (wardHierarchy V).Character) (r : ℝ)
    (o : YangMills.Spacetime) (φ : YangMills.WilsonFamily.SeparatedTest 1) (a b : YM.Axis) :
    (∫ x : YangMills.Points 1, φ x * marked V s r o
      ((r^4 : ℂ) • (wardHierarchy V).stress a b) (emptyTail V) x) =
      (r^4 : ℂ) * ((∫ x : YangMills.Points 1, φ x) *
        atOrigin V s ((wardHierarchy V).stress a b)) := by
  simp_rw [atEveryHome,originLinear]
  rw [integral_mul_const]
  ring

theorem conservationTest (V : Vision E ξ) (s : Option (wardHierarchy V).Character)
    (r : ℝ) (hr : 0 < r) (o : YangMills.Spacetime) {n : ℕ}
    (q : Fin n → (wardHierarchy V).Tag) (b : YM.Axis) (φ : YangMills.WilsonFamily.SeparatedTest (n+1)) :
    (∑ a : YM.Axis, ∫ x : YangMills.Points (n+1),
      YangMills.Ward.firstDerivative a (fun y => φ y) x *
        marked V s r o ((r^4 : ℂ) • (wardHierarchy V).stress a b) q x) = 0 := by
  let f (a : YM.Axis) : YangMills.Points (n+1) → ℂ :=
    marked V s r o ((r^4 : ℂ) • (wardHierarchy V).stress a b) q
  have hs (a : YM.Axis) x (hx : x ∈ tsupport φ) : ContDiffAt ℝ ∞ (f a) x :=
    shapedSmooth V s (Fin.cons ⟨4,(r^4 : ℂ) • (wardHierarchy V).stress a b⟩ q)
      r hr o x (φ.tsupport_subset hx)
  have hb (a : YM.Axis) := testParts φ a (f a) (hs a)
  change (∑ a : YM.Axis, ∫ x : YangMills.Points (n+1),
    YangMills.Ward.firstDerivative a (fun y => φ y) x * f a x) = 0
  simp_rw [fun a => (hb a).2, Finset.sum_neg_distrib]
  rw [← integral_finsetSum _ (fun a _ => (hb a).1)]
  have zeroSum (x : YangMills.Points (n+1)) :
      (∑ a : YM.Axis, φ x * YangMills.Ward.firstDerivative a (f a) x) = 0 := by
    by_cases hx : x ∈ tsupport φ
    · have hz (a : YM.Axis) := derivativeAtShape V s
          (Fin.cons ⟨4,(r^4 : ℂ) • (wardHierarchy V).stress a b⟩ q) r hr o x (φ.tsupport_subset hx) a
      rw [← Finset.mul_sum]
      simp_rw [show ∀ a, YangMills.Ward.firstDerivative a (f a) x = _ from hz, ← Finset.mul_sum]
      rw [separatedConservation V s q (sites r o x)
        (YM.Answer.ContinuumLimit.ElectedMeasurement.centerSeparated hr o x (φ.tsupport_subset hx)) (r^4 : ℂ) b]
      simp
    · have he : φ x = 0 := by
        by_contra hn
        exact hx (subset_tsupport _ (show x ∈ Function.support (fun y => φ y) from hn))
      simp [he]
  simp_rw [zeroSum]
  simp

def density (V : Vision E ξ) (s : Option (wardHierarchy V).Character) {d n : ℕ}
    (v : (wardHierarchy V).Field d) (q : Fin n → (wardHierarchy V).Tag)
    (r : ℝ) (o : YangMills.Spacetime) (P : Shell n) (a b : YM.Axis)
    (z : YangMills.Spacetime) (x : YangMills.Points (n+1)) : ℂ :=
  Complex.ofReal (YangMills.Maxwell.partialD a P.cutoff z) *
    marked V s r o ((r^4 : ℂ) • (wardHierarchy V).stress a b)
      (Fin.cons ⟨d,v⟩ q) (YangMills.Ward.prepend z x)

theorem pointwiseFlux (V : Vision E ξ) (s : Option (wardHierarchy V).Character) {d n : ℕ}
    (v : (wardHierarchy V).Field d) (q : Fin n → (wardHierarchy V).Tag)
    (r : ℝ) (hr : 0 < r) (o : YangMills.Spacetime) (P : Shell n) (b : YM.Axis)
    (x : YangMills.Points (n+1)) (hx : x ∈ tsupport (fun y => P.translation y)) :
    -(∑ a : YM.Axis, ∫ z, density V s v q r o P a b z x) =
      YangMills.Ward.firstDerivative b (fun y =>
        (wardHierarchy V).correlation s (Fin.cons ⟨d,v⟩ q) (sites r o y)) x := by
  let χ := PhysicalMatching.H7StandaloneScaledTranslationWindow.transported r hr o P.cutoff
  have hw := PhysicalMatching.H7StandaloneScaledTranslationWindow.window r hr o x (P.window x hx)
  have h := PhysicalMatching.H7StandaloneScaledTranslationWindow.original V s r hr o x v q (P.window x hx) b
  have hxr := YM.Answer.ContinuumLimit.ElectedMeasurement.centerSeparated hr o x (P.translation.tsupport_subset hx)
  calc
    _ = (r : ℂ) * (wardHierarchy V).translationFlux s (sites r o x) v q χ b := by
      rw [show (wardHierarchy V).translationFlux s (sites r o x) v q χ b = _ from h,
        mul_neg, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro a _
      rw [Complex.real_smul, ← mul_assoc, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with z
      unfold density marked
      rw [firstSlot_eq, firstSlot_eq, map_smul]
      simp only [smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_pow]
      field_simp [hr.ne']
    _ = _ := by
      rw [(PhysicalMatching.H7StandaloneAppointedPublicWardRows.original V).translation s
        (sites r o x) hxr v q χ hw b]
      exact (derivativeAtShape V s (Fin.cons ⟨d,v⟩ q) r hr o x (P.translation.tsupport_subset hx) b).symm

theorem integrableFlux (V : Vision E ξ) (s : Option (wardHierarchy V).Character) {d n : ℕ}
    (v : (wardHierarchy V).Field d) (q : Fin n → (wardHierarchy V).Tag)
    (r : ℝ) (hr : 0 < r) (o : YangMills.Spacetime) (P : Shell n) (a b : YM.Axis) :
    Integrable (fun u : YangMills.Spacetime × YangMills.Points (n+1) =>
      P.translation u.2 * density V s v q r o P a b u.1 u.2) := by
  let tags := Fin.cons (α := fun _ : Fin ((n+1)+1) => (wardHierarchy V).Tag)
    ⟨4,(r^4 : ℂ) • (wardHierarchy V).stress a b⟩ (Fin.cons ⟨d,v⟩ q)
  let f (u : YangMills.Spacetime × YangMills.Points (n+1)) :=
      (wardHierarchy V).correlation s tags (sites r o (YangMills.Ward.prepend u.1 u.2))
  have hprepend : Continuous (fun u : YangMills.Spacetime × YangMills.Points (n+1) => YangMills.Ward.prepend u.1 u.2) := by
    unfold YangMills.Ward.prepend
    apply (PiLp.continuous_toLp 2 (fun _ : Fin ((n+1)+1) => YangMills.Spacetime)).comp
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact continuous_fst
    · exact (PiLp.continuous_apply 2 (fun _ : Fin (n+1) => YangMills.Spacetime) j).comp continuous_snd
  have h := shellIntegrable P a f (by
    intro u hu
    have hfield : ContinuousAt (fun y : YangMills.Points ((n+1)+1) =>
        (wardHierarchy V).correlation s tags (sites r o y)) (YangMills.Ward.prepend u.1 u.2) :=
      (shapedSmooth V s tags r hr o (YangMills.Ward.prepend u.1 u.2) hu).continuousAt
    have hchart : ContinuousAt (fun w : YangMills.Spacetime × YangMills.Points (n+1) =>
        YangMills.Ward.prepend w.1 w.2) u := hprepend.continuousAt
    exact ContinuousAt.comp (f := fun w : YangMills.Spacetime × YangMills.Points (n+1) =>
      YangMills.Ward.prepend w.1 w.2) (x := u) hfield hchart)
  simpa only [weight, density, marked, mul_assoc] using h

theorem translationTest (V : Vision E ξ) (s : Option (wardHierarchy V).Character) {d n : ℕ}
    (v : (wardHierarchy V).Field d) (q : Fin n → (wardHierarchy V).Tag)
    (r : ℝ) (hr : 0 < r) (o : YangMills.Spacetime) (P : Shell n) (b : YM.Axis) :
    -(∑ a : YM.Axis, ∫ u : YangMills.Spacetime × YangMills.Points (n+1),
      P.translation u.2 * density V s v q r o P a b u.1 u.2 ∂(volume.prod volume)) =
      -(∫ x : YangMills.Points (n+1), YangMills.Ward.firstDerivative b (fun y => P.translation y) x *
        (wardHierarchy V).correlation s (Fin.cons ⟨d,v⟩ q) (sites r o x)) := by
  let f := fun x => (wardHierarchy V).correlation s (Fin.cons ⟨d,v⟩ q) (sites r o x)
  let w (a : YM.Axis) (u : YangMills.Spacetime × YangMills.Points (n+1)) :=
    P.translation u.2 * density V s v q r o P a b u.1 u.2
  have hi (a : YM.Axis) : Integrable (w a) (volume.prod volume) := integrableFlux V s v q r hr o P a b
  have hφ := testParts P.translation b f (fun x hx =>
    shapedSmooth V s (Fin.cons ⟨d,v⟩ q) r hr o x (P.translation.tsupport_subset hx))
  have inner (x : YangMills.Points (n+1)) :
      -(∑ a : YM.Axis, ∫ z : YangMills.Spacetime, w a (z,x)) = P.translation x * YangMills.Ward.firstDerivative b f x := by
    by_cases hx : x ∈ tsupport (fun y => P.translation y)
    · simp_rw [w, integral_const_mul, ← Finset.mul_sum, ← mul_neg]
      exact congrArg (fun z => P.translation x * z) (pointwiseFlux V s v q r hr o P b x hx)
    · have he : P.translation x = 0 := by
        by_contra hn; exact hx (subset_tsupport _ hn)
      simp [w,he]
  change -(∑ a : YM.Axis, ∫ u : YangMills.Spacetime × YangMills.Points (n+1), w a u ∂(volume.prod volume)) = _
  calc
    _ = ∫ x : YangMills.Points (n+1), -(∑ a : YM.Axis, ∫ z : YangMills.Spacetime, w a (z,x)) := by
      simp_rw [integral_prod_symm _ (hi _)]
      rw [integral_neg, integral_finsetSum _ (fun a _ => (hi a).integral_prod_right)]
    _ = ∫ x : YangMills.Points (n+1), P.translation x * YangMills.Ward.firstDerivative b f x := by simp_rw [inner]
    _ = _ := by rw [hφ.2,neg_neg]

end PhysicalMatching.H7StandaloneArbitraryWardTestReadings
