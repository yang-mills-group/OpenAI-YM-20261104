import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7StandaloneSmearedConservation
import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7StandaloneVacuumWardReading
import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7StandaloneTranslationTestSupport
import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7StandaloneAppointedTranslationReading
import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7StandaloneFiniteWardMatrix
namespace PhysicalMatching.H7StandaloneFourWardBalance
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
open PhysicalMatching.H7StandaloneAppointedWardBalance PhysicalMatching.H7StandaloneFiniteWardMatrix
open scoped BigOperators Classical Topology

theorem markedSum (V : Vision E ξ) (phase : Option (wardHierarchy V).Character)
    (r : ℝ) (o : YangMills.Spacetime) {n : ℕ} (q : Fin n → (wardHierarchy V).Tag)
    (x : YangMills.Points (n+1)) (u : Fin 4 → ℂ) (w : Fin 4 → (wardHierarchy V).Field 4) :
    marked V phase r o (∑ m, u m • w m) q x =
      ∑ m, u m * marked V phase r o (w m) q x := by
  simp only [marked, firstSlot_eq, map_sum, map_smul, smul_eq_mul]

theorem integralSum {α : Type*} [MeasureSpace α]
    (u : Fin 4 → ℂ) (w g : α → ℂ) (f : Fin 4 → α → ℂ)
    (he : ∀ x, g x = ∑ m, u m * f m x)
    (hi : ∀ m, Integrable (fun x => w x * f m x)) :
    (∫ x, w x * g x) = ∑ m, u m * ∫ x, w x * f m x := by
  calc
    (∫ x, w x * g x) = ∫ x, ∑ m, u m * (w x * f m x) := by
      apply integral_congr_ae
      filter_upwards with x
      rw [he, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      ring
    _ = ∑ m, ∫ x, u m * (w x * f m x) := by
      rw [integral_finsetSum]
      intro m _
      exact (hi m).const_mul _
    _ = _ := by simp only [integral_const_mul]

theorem testDue (V : Vision E ξ) (phase : Option (wardHierarchy V).Character)
    (r : ℝ) (hr : 0 < r) (o : YangMills.Spacetime) {n : ℕ} (q : Fin n → (wardHierarchy V).Tag)
    (v : (wardHierarchy V).Field 4) (w : YangMills.Points (n+1) → ℂ)
    (hw : Continuous w) (hc : HasCompactSupport w) (hs : tsupport w ⊆ YM.conf (n+1)) :
    Integrable (fun x => w x * marked V phase r o v q x) := by
  let F := fun x => w x * marked V phase r o v q x
  have hm : ContinuousOn (fun x => marked V phase r o v q x) (tsupport w) := by
    intro x hx
    exact (PhysicalMatching.H7StandaloneSmearedConservation.shapedSmooth V phase
      (Fin.cons ⟨4,v⟩ q) r hr o x (hs hx)).continuousAt.continuousWithinAt
  have intOn : IntegrableOn F (tsupport w) := (hw.continuousOn.mul hm).integrableOn_compact hc
  have eqn : F = (tsupport w).indicator F := by
    funext x
    by_cases hx : x ∈ tsupport w
    · simp [hx]
    · have hz : w x = 0 := notMem_support.mp (fun h => hx (subset_tsupport _ h))
      simp [F,hx,hz]
  change Integrable F
  rw [eqn]
  exact (integrable_indicator_iff hc.measurableSet).2 intOn

theorem derivativeDue (V : Vision E ξ) (phase : Option (wardHierarchy V).Character)
    (r : ℝ) (hr : 0 < r) (o : YangMills.Spacetime) {n : ℕ} (q : Fin n → (wardHierarchy V).Tag)
    (v : (wardHierarchy V).Field 4) (φ : YangMills.WilsonFamily.SeparatedTest (n+1)) (a : YM.Axis) :
    Integrable (fun x => YangMills.Ward.firstDerivative a (fun y => φ y) x * marked V phase r o v q x) := by
  let e : YangMills.Points (n+1) := PiLp.single 2 0 (EuclideanSpace.single a 1)
  apply testDue V phase r hr o q v
  · exact (φ.contDiff.continuous_fderiv (by simp)).clm_apply continuous_const
  · exact φ.hasCompactSupport.fderiv_apply ℝ e
  · exact (tsupport_fderiv_apply_subset ℝ e).trans φ.tsupport_subset

private theorem continuousPrepend : Continuous (fun z : YangMills.Spacetime × YangMills.Points 2 => YangMills.Ward.prepend z.1 z.2) := by
  unfold YangMills.Ward.prepend
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => YangMills.Spacetime)).comp
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact continuous_fst
  · exact (PiLp.continuous_apply 2 (fun _ : Fin 2 => YangMills.Spacetime) j).comp continuous_snd

theorem fluxDue (V : Vision E ξ) (Z : WilsonPrescription g.core)
    (phase : Option (wardHierarchy V).Character) (r : ℝ) (hr : 0 < r)
    (o : YangMills.Spacetime) (P : Pupils) (a : YM.Axis) (v : (wardHierarchy V).Field 4) :
    Integrable (fun z : YangMills.Spacetime × YangMills.Points 2 =>
      PhysicalMatching.H7StandaloneTranslationTestSupport.weight P a z *
        marked V phase r o v (fun _ : Fin 2 => probeTag V Z r 0) (YangMills.Ward.prepend z.1 z.2)) := by
  apply PhysicalMatching.H7StandaloneTranslationTestSupport.original P a
  intro z hz
  let m : YangMills.Spacetime × YangMills.Points 2 → YangMills.Points 3 := fun y => YangMills.Ward.prepend y.1 y.2
  let q : Fin 3 → (wardHierarchy V).Tag := Fin.cons ⟨4,v⟩ (fun _ : Fin 2 => probeTag V Z r 0)
  have h : ContinuousAt (fun y : YangMills.Points 3 => (wardHierarchy V).correlation phase q (sites r o y)) (m z) :=
    (PhysicalMatching.H7StandaloneSmearedConservation.shapedSmooth V phase q r hr o (m z) hz).continuousAt
  have hm : ContinuousAt m z := continuousPrepend.continuousAt
  exact h.comp hm

theorem vacuumLine (V : Vision E ξ) (Z : WilsonPrescription g.core)
    (phase : Option (wardHierarchy V).Character) (r : ℝ) (hr : 0 < r)
    (o : YangMills.Spacetime) (P : Pupils) (u : Fin 4 → ℂ) :
    vacuum V phase r o P (fun a b => ∑ m, u m • physicalColumns V Z r a b m) =
      ∑ m, u m * vacuum V phase r o P (fun a b => physicalColumns V Z r a b m) := by
  unfold vacuum
  apply integralSum
  · intro x
    apply markedSum
  · intro m
    exact testDue V phase r hr o _ _ _ P.vacuum.continuous P.vacuum.hasCompactSupport P.vacuum.tsupport_subset

theorem conservationLine (V : Vision E ξ) (Z : WilsonPrescription g.core)
    (phase : Option (wardHierarchy V).Character) (r : ℝ) (hr : 0 < r)
    (o : YangMills.Spacetime) (P : Pupils) (u : Fin 4 → ℂ) (row : Fin 2) :
    conservation V Z phase r o P (fun a b => ∑ m, u m • physicalColumns V Z r a b m) row =
      ∑ m, u m * conservation V Z phase r o P (fun a b => physicalColumns V Z r a b m) row := by
  let f := fun (j : Fin 2) (a : YM.Axis) (m : Fin 4) => ∫ x : YangMills.Points 2,
    YangMills.Ward.firstDerivative a (fun y => P.conservation row j y) x *
      marked V phase r o (physicalColumns V Z r a 0 m) (fun _ : Fin 1 => probeTag V Z r j) x
  calc
    _ = ∑ j : Fin 2, ∑ a : YM.Axis, ∑ m, u m * f j a m := by
      unfold conservation
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro a _
      apply integralSum
      · intro x
        apply markedSum
      · intro m
        exact derivativeDue V phase r hr o _ _ (P.conservation row j) a
    _ = ∑ j : Fin 2, ∑ m, ∑ a : YM.Axis, u m * f j a m := by
      apply Finset.sum_congr rfl
      intro j _
      exact Finset.sum_comm
    _ = ∑ m, ∑ j : Fin 2, ∑ a : YM.Axis, u m * f j a m := Finset.sum_comm
    _ = _ := by simp only [conservation, f, Finset.mul_sum]

theorem fluxLine (V : Vision E ξ) (Z : WilsonPrescription g.core)
    (phase : Option (wardHierarchy V).Character) (r : ℝ) (hr : 0 < r)
    (o : YangMills.Spacetime) (P : Pupils) (u : Fin 4 → ℂ) :
    flux V Z phase r o P (fun a b => ∑ m, u m • physicalColumns V Z r a b m) =
      ∑ m, u m * flux V Z phase r o P (fun a b => physicalColumns V Z r a b m) := by
  let f := fun (a : YM.Axis) (m : Fin 4) => ∫ z : YangMills.Spacetime × YangMills.Points 2,
    PhysicalMatching.H7StandaloneTranslationTestSupport.weight P a z *
      marked V phase r o (physicalColumns V Z r a 0 m) (fun _ : Fin 2 => probeTag V Z r 0)
        (YangMills.Ward.prepend z.1 z.2)
  calc
    _ = -(∑ a : YM.Axis, ∑ m, u m * f a m) := by
      unfold flux
      congr 1
      apply Finset.sum_congr rfl
      intro a _
      apply integralSum
      · intro z
        apply markedSum
      · intro m
        exact fluxDue V Z phase r hr o P a _
    _ = -(∑ m, ∑ a : YM.Axis, u m * f a m) := by rw [Finset.sum_comm]
    _ = _ := by simp only [flux, f, PhysicalMatching.H7StandaloneTranslationTestSupport.weight,
      mul_neg, Finset.mul_sum, Finset.sum_neg_distrib]

theorem frameSpan (V : Vision E ξ) (Z : WilsonPrescription g.core) (r : ℝ) (u : Fin 4 → ℂ)
    (span : ∀ a b, measuredStress V Z r a b = ∑ m, u m • columns H a b m) :
    (fun a b => (r^4 : ℂ) • (wardHierarchy V).stress a b) =
      (fun a b => ∑ m, u m • physicalColumns V Z r a b m) := by
  funext a b
  calc
    _ = YM.Answer.ContinuumLimit.ElectedMeasurement.frame V Z r 4 (measuredStress V Z r a b) := (frameReconstruction V Z r a b).symm
    _ = _ := by rw [span a b]; simp only [map_sum, map_smul, physicalColumns]

theorem original (V : Vision E ξ) (Z : WilsonPrescription g.core)
    (phase : Option (wardHierarchy V).Character) (r : ℝ) (hr : 0 < r)
    (o : YangMills.Spacetime) (P : Pupils) (u : Fin 4 → ℂ)
    (span : ∀ a b, measuredStress V Z r a b = ∑ m, u m • columns H a b m) :
    act (matrix V Z phase r o P) u - rightSide V Z phase r o P =
      ![(r^4 : ℂ) * ((∫ x : YangMills.Points 1, P.vacuum x) *
        PhysicalMatching.H7StandaloneVacuumWardReading.atOrigin V phase ((wardHierarchy V).stress 0 0)),0,0,0] := by
  have hspan := frameSpan V Z r u span
  have v := PhysicalMatching.H7StandaloneVacuumWardReading.original V phase r o P
  have c0 := PhysicalMatching.H7StandaloneSmearedConservation.original V Z phase r hr o P 0
  have c1 := PhysicalMatching.H7StandaloneSmearedConservation.original V Z phase r hr o P 1
  have t := PhysicalMatching.H7StandaloneAppointedTranslationReading.original V Z phase r hr o P
  rw [hspan, vacuumLine V Z phase r hr o P u] at v
  rw [hspan, conservationLine V Z phase r hr o P u 0] at c0
  rw [hspan, conservationLine V Z phase r hr o P u 1] at c1
  rw [hspan, fluxLine V Z phase r hr o P u] at t
  ext i
  fin_cases i <;> simp [PhysicalMatching.H7StandaloneFiniteWardMatrix.act, PhysicalMatching.H7StandaloneFourSmearedWardReadings.matrix, PhysicalMatching.H7StandaloneFourSmearedWardReadings.readings, PhysicalMatching.H7StandaloneFourSmearedWardReadings.rightSide, mul_comm, v, c0, c1, t]
end PhysicalMatching.H7StandaloneFourWardBalance

