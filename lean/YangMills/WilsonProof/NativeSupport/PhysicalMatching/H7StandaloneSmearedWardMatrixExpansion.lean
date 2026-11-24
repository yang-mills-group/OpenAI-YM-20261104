import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7StandaloneFiledWardMatrixCoefficients
import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7StandaloneFiniteWardMatrix
import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7StandaloneTestedCorrelationExpansion
import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7StandaloneTranslationTestSupport
import YM.Integration.WilsonGraphPublishedShapeEstimate

set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
namespace PhysicalMatching.H7StandaloneSmearedWardMatrixExpansion
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
open YangMills.WilsonFamily
open MeasureTheory


open PhysicalMatching.H7StandaloneFourSmearedWardReadings
open YM.Integration.WilsonGraphPublishedShapeEstimate
open YM.Answer.ContinuumLimit.Vision
open scoped Topology
local notation "B₀" => YangMills.maxwellReference g

open PhysicalMatching.H7StandaloneIntegratedWardEntryBounds

open PhysicalMatching.H7StandaloneFiledWardMatrixCoefficients
open YangMills.Matching.CorrelationOnly
open PhysicalMatching.H7StandaloneFiniteWardMatrix

def RowPrice (clock : ℝ → ℝ) (p : ℕ) (actual : ℝ → ℂ) (filed : ℕ → ℂ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ r : ℝ in 𝓝[>] 0,
    ‖actual r - ∑ k : Fin (p+1), (clock r : ℂ)^k.val * filed k.val‖ ≤ C * |clock r|^(p+1)

theorem zeroPrice (clock : ℝ → ℝ) (p : ℕ) : RowPrice clock p (fun _ => 0) (fun _ => 0) := by
  exact ⟨0,le_rfl,Filter.Eventually.of_forall fun _ => by simp⟩

theorem negPrice {clock : ℝ → ℝ} {p : ℕ} {a : ℝ → ℂ} {b : ℕ → ℂ}
    (h : RowPrice clock p a b) : RowPrice clock p (fun r => -a r) (fun k => -b k) := by
  obtain ⟨C,hC,late⟩ := h
  refine ⟨C,hC,late.mono fun r hr => ?_⟩
  simpa only [mul_neg,Finset.sum_neg_distrib,neg_sub_neg,norm_sub_rev] using hr

theorem sumPrice {ι : Type*} [Fintype ι] {clock : ℝ → ℝ} {p : ℕ}
    {a : ι → ℝ → ℂ} {b : ι → ℕ → ℂ} (h : ∀ i, RowPrice clock p (a i) (b i)) :
    RowPrice clock p (fun r => ∑ i, a i r) (fun k => ∑ i, b i k) := by
  choose C hC hlate using h
  refine ⟨∑ i, C i,Finset.sum_nonneg fun i _ => hC i,?_⟩
  filter_upwards [Filter.eventually_all.2 hlate] with r hr
  have eqn : (∑ i, a i r) - (∑ k : Fin (p+1), (clock r : ℂ)^k.val * ∑ i, b i k.val) =
      ∑ i, (a i r - ∑ k : Fin (p+1), (clock r : ℂ)^k.val * b i k.val) := by
    rw [Finset.sum_sub_distrib]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
  rw [eqn,Finset.sum_mul]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hr i)

theorem filedCrops (V : Vision E ξ) (Z : WilsonPrescription g.core) (Q : Perspective H Z true)
    (shapes : ReferenceShape Z V Q) {n : ℕ} (cap : ℕ) (d : Caps n) (within : ∀ i, d i ≤ cap)
    (v : FVA2.GradedFar.Inputs g.core d) (phase : Option (wardHierarchy V).Character) (o : E4) :
    CompactShapeCrops (ElectedMeasurement.clock V Z)
      (fun r x => (wardHierarchy V).correlation phase (ElectedMeasurement.inputs V Z r d v) (sites r o x))
      (groupCoefficient Z Q d v) := by
  intro p K hK clear
  obtain ⟨A,hA,late⟩ := shapes n cap K hK clear p 0
  refine ⟨A * (∏ i, YangMills.Matching.sectorMass (B := B₀) (v i)),
    mul_nonneg hA (Finset.prod_nonneg fun i _ => YangMills.Matching.sectorMass_nonneg (B := B₀) (v i)), ?_⟩
  exact late.mono fun r hr x hx => hr d within v phase o x hx

theorem weightedIntegrable {α : Type*} [NormedAddCommGroup α] [NormedSpace ℝ α]
    [FiniteDimensional ℝ α] [MeasureSpace α] [BorelSpace α]
    [IsLocallyFiniteMeasure (volume : Measure α)] {n : ℕ} (w : α → ℂ)
    (hw : Continuous w) (hc : HasCompactSupport w) (sh : α → YangMills.Points n) (hs : Continuous sh)
    (f : YangMills.Points n → ℂ) (hf : ContinuousOn f (sh '' tsupport w)) : Integrable (fun z => w z * f (sh z)) := by
  let F := fun z => w z * f (sh z)
  have inside : MapsTo sh (tsupport w) (sh '' tsupport w) := fun z hz => ⟨z,hz,rfl⟩
  have onS : IntegrableOn F (tsupport w) :=
    (hw.continuousOn.mul (hf.comp hs.continuousOn inside)).integrableOn_compact hc
  have eqn : F = (tsupport w).indicator F := by
    funext z
    by_cases hz : z ∈ tsupport w
    · simp [hz]
    · have zero : w z = 0 := by
        by_contra hn
        exact hz (subset_tsupport w hn)
      simp [hz,F,zero]
  change Integrable F
  rw [eqn]
  exact (integrable_indicator_iff hc.measurableSet).2 onS

theorem integralPrice {α : Type*} [NormedAddCommGroup α] [NormedSpace ℝ α]
    [FiniteDimensional ℝ α] [MeasureSpace α] [BorelSpace α]
    [IsLocallyFiniteMeasure (volume : Measure α)] (V : Vision E ξ) (Z : WilsonPrescription g.core)
    (Q : Perspective H Z true) (shapes : ReferenceShape Z V Q)
    (phase : Option (wardHierarchy V).Character) (o : E4) (p : ℕ) {n : ℕ}
    (d : Caps n) (within : ∀ i, d i ≤ 4) (v : FVA2.GradedFar.Inputs g.core d)
    (w : α → ℂ) (hw : Continuous w) (hc : HasCompactSupport w) (sh : α → YangMills.Points n)
    (hs : Continuous sh) (clear : ∀ z ∈ tsupport w, sh z ∈ conf n) :
    RowPrice (ElectedMeasurement.clock V Z) p
      (fun r => ∫ z, w z * (wardHierarchy V).correlation phase (ElectedMeasurement.inputs V Z r d v) (sites r o (sh z)))
      (fun k => ∫ z, w z * groupCoefficient Z Q d v k (sh z)) := by
  let K := sh '' tsupport w
  have hK : IsCompact K := hc.image hs
  have sep : K ⊆ conf n := by rintro _ ⟨z,hz,rfl⟩; exact clear z hz
  have crops := filedCrops V Z Q shapes 4 d within v phase o
  have ib (k : ℕ) : Integrable (fun z => w z * groupCoefficient Z Q d v k (sh z)) :=
    weightedIntegrable w hw hc sh hs _ (coefficientContinuousOn (ElectedMeasurement.positive V Z Q) crops K hK sep k)
  obtain ⟨A,hA,priced⟩ := compactEntry volume V Z Q (referenceCompact Z V Q shapes) 4 p w sh K hK sep
    (fun z hz => ⟨z,hz,rfl⟩) (hw.norm.integrable_of_hasCompactSupport hc.norm)
  obtain ⟨B,hB,smooth⟩ := crops p K hK sep
  let mass := ∏ i, YangMills.Matching.sectorMass (B := B₀) (v i)
  let C := (∫ z, ‖w z‖) * (A * mass)
  refine ⟨max 0 C,le_max_left _ _,?_⟩
  filter_upwards [priced,smooth] with r hr hsr
  have ia := weightedIntegrable w hw hc sh hs
    (fun x => (wardHierarchy V).correlation phase (ElectedMeasurement.inputs V Z r d v) (sites r o x))
    (fun x hx => (hsr x hx).1.continuousAt.continuousWithinAt)
  have h := hr d within v phase o
  rw [integralResidual volume V Z Q d v phase r o p w sh ia (fun k => ib k.val)] at h
  calc
    _ ≤ (∫ z, ‖w z‖) * (A * mass * |ElectedMeasurement.clock V Z r|^(p+1)) := h
    _ = C * |ElectedMeasurement.clock V Z r|^(p+1) := by simp only [C,mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg (abs_nonneg _) _)

theorem derivativeWeight {n : ℕ} (φ : YangMills.WilsonFamily.SeparatedTest (n+1)) (a : YM.Axis) :
    Continuous (YangMills.Ward.firstDerivative a (fun x => φ x)) ∧
    HasCompactSupport (YangMills.Ward.firstDerivative a (fun x => φ x)) ∧
    tsupport (YangMills.Ward.firstDerivative a (fun x => φ x)) ⊆ conf (n+1) := by
  let e : YangMills.Points (n+1) := PiLp.single 2 0 (EuclideanSpace.single a 1)
  have hφ : ContDiff ℝ ∞ (fun x => φ x) := φ.contDiff
  exact ⟨(hφ.continuous_fderiv (by simp)).clm_apply continuous_const,
    φ.hasCompactSupport.fderiv_apply ℝ e,(tsupport_fderiv_apply_subset ℝ e).trans φ.tsupport_subset⟩

theorem markedPrice {α : Type*} [NormedAddCommGroup α] [NormedSpace ℝ α]
    [FiniteDimensional ℝ α] [MeasureSpace α] [BorelSpace α]
    [IsLocallyFiniteMeasure (volume : Measure α)] (V : Vision E ξ) (Z : WilsonPrescription g.core)
    (Q : Perspective H Z true) (shapes : ReferenceShape Z V Q)
    (phase : Option (wardHierarchy V).Character) (o : E4) (p : ℕ) (a b : YM.Axis) (m : Fin 4)
    {n : ℕ} (t : Fin n → Fin 2) (w : α → ℂ) (hw : Continuous w) (hc : HasCompactSupport w)
    (sh : α → YangMills.Points (n+1)) (hs : Continuous sh) (clear : ∀ z ∈ tsupport w, sh z ∈ conf (n+1)) :
    RowPrice (ElectedMeasurement.clock V Z) p
      (fun r => ∫ z, w z * marked V phase r o (physicalColumns V Z r a b m) (fun i => probeTag V Z r (t i)) (sh z))
      (fun k => ∫ z, w z * groupMarked Z Q k a b m t (sh z)) := by
  simpa only [markedInputs,marked,groupMarked] using integralPrice V Z Q shapes phase o p
    (fun _ => 4) (fun _ => le_rfl) (markedLabels H a b m t) w hw hc sh hs clear

theorem vacuumPrice (V : Vision E ξ) (Z : WilsonPrescription g.core) (Q : Perspective H Z true)
    (shapes : ReferenceShape Z V Q) (phase : Option (wardHierarchy V).Character) (o : E4) (p : ℕ)
    (P : Pupils) (m : Fin 4) :
    RowPrice (ElectedMeasurement.clock V Z) p
      (fun r => vacuum V phase r o P (fun a b => physicalColumns V Z r a b m))
      (fun k => vacuumEntry Z Q P k m) := by
  have h := markedPrice V Z Q shapes phase o p 0 0 m (fun i : Fin 0 => Fin.elim0 i)
    (fun x => P.vacuum x) P.vacuum.continuous P.vacuum.hasCompactSupport id continuous_id
    (fun x hx => P.vacuum.tsupport_subset hx)
  have hz (r : ℝ) : (fun i : Fin 0 => probeTag V Z r (Fin.elim0 i)) =
      (fun i : Fin 0 => (Fin.elim0 i : (wardHierarchy V).Tag)) := funext fun i => Fin.elim0 i
  simpa only [vacuum,vacuumEntry,hz,id_eq] using h

theorem conservationPrice (V : Vision E ξ) (Z : WilsonPrescription g.core) (Q : Perspective H Z true)
    (shapes : ReferenceShape Z V Q) (phase : Option (wardHierarchy V).Character) (o : E4) (p : ℕ)
    (P : Pupils) (row : Fin 2) (m : Fin 4) :
    RowPrice (ElectedMeasurement.clock V Z) p
      (fun r => conservation V Z phase r o P (fun a b => physicalColumns V Z r a b m) row)
      (fun k => conservationEntry Z Q P k row m) := by
  apply sumPrice
  intro j
  apply sumPrice
  intro a
  obtain ⟨hw,hc,clear⟩ := derivativeWeight (P.conservation row j) a
  exact markedPrice V Z Q shapes phase o p a 0 m (fun _ : Fin 1 => j) _ hw hc id continuous_id clear

theorem fluxPrice (V : Vision E ξ) (Z : WilsonPrescription g.core) (Q : Perspective H Z true)
    (shapes : ReferenceShape Z V Q) (phase : Option (wardHierarchy V).Character) (o : E4) (p : ℕ)
    (P : Pupils) (m : Fin 4) :
    RowPrice (ElectedMeasurement.clock V Z) p
      (fun r => flux V Z phase r o P (fun a b => physicalColumns V Z r a b m))
      (fun k => fluxEntry Z Q P k m) := by
  apply negPrice
  apply sumPrice
  intro a
  exact markedPrice V Z Q shapes phase o p a 0 m (fun _ : Fin 2 => 0)
    (H7StandaloneTranslationTestSupport.weight P a) (H7StandaloneTranslationTestSupport.smoothWeight P a)
    (H7StandaloneTranslationTestSupport.compact P a) _ prependContinuous
    (fun z hz => H7StandaloneTranslationTestSupport.separated P a hz)

theorem matrixRows (V : Vision E ξ) (Z : WilsonPrescription g.core) (Q : Perspective H Z true)
    (shapes : ReferenceShape Z V Q) (phase : Option (wardHierarchy V).Character) (o : E4) (p : ℕ)
    (P : Pupils) (i m : Fin 4) :
    RowPrice (ElectedMeasurement.clock V Z) p (fun r => matrix V Z phase r o P i m)
      (fun k => matrixCoefficients Z Q P k i m) := by
  fin_cases i
  · exact vacuumPrice V Z Q shapes phase o p P m
  · exact conservationPrice V Z Q shapes phase o p P 0 m
  · exact conservationPrice V Z Q shapes phase o p P 1 m
  · exact fluxPrice V Z Q shapes phase o p P m

theorem rightRows (V : Vision E ξ) (Z : WilsonPrescription g.core) (Q : Perspective H Z true)
    (shapes : ReferenceShape Z V Q) (phase : Option (wardHierarchy V).Character) (o : E4) (p : ℕ)
    (P : Pupils) (i : Fin 4) :
    RowPrice (ElectedMeasurement.clock V Z) p (fun r => rightSide V Z phase r o P i)
      (fun k => rhsCoefficients Z Q P k i) := by
  fin_cases i
  · exact zeroPrice _ _
  · exact zeroPrice _ _
  · exact zeroPrice _ _
  · apply negPrice
    obtain ⟨hw,hc,clear⟩ := derivativeWeight P.translation 0
    exact integralPrice V Z Q shapes phase o p (fun _ : Fin 2 => 4) (fun _ => le_rfl)
      (fun _ => probes H 0) _ hw hc id continuous_id clear

theorem original (V : Vision E ξ) (Z : WilsonPrescription g.core) (Q : Perspective H Z true)
    (shapes : ReferenceShape Z V Q) (phase : Option (wardHierarchy V).Character) (o : E4)
    (p : ℕ) (P : Pupils) : ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ᶠ r : ℝ in 𝓝[>] 0,
    matrixSize (matrix V Z phase r o P - ∑ k : Fin (p+1), (ElectedMeasurement.clock V Z r : ℂ)^k.val •
      matrixCoefficients Z Q P k.val) ≤ C * |ElectedMeasurement.clock V Z r|^(p+1) ∧
    size (rightSide V Z phase r o P - ∑ k : Fin (p+1), (ElectedMeasurement.clock V Z r : ℂ)^k.val •
      rhsCoefficients Z Q P k.val) ≤ D * |ElectedMeasurement.clock V Z r|^(p+1) := by
  choose C hC lateC using matrixRows V Z Q shapes phase o p P
  choose D hD lateD using rightRows V Z Q shapes phase o p P
  refine ⟨∑ i, ∑ m, C i m,∑ i, D i,Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun m _ => hC i m,
    Finset.sum_nonneg fun i _ => hD i,?_⟩
  have hp := Filter.eventually_all.2 fun i => Filter.eventually_all.2 (lateC i)
  filter_upwards [hp,Filter.eventually_all.2 lateD] with r hr hs
  constructor
  · unfold matrixSize
    simp only [Matrix.sub_apply,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun m _ => hr i m
  · unfold size
    simp only [Pi.sub_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ => hs i

end PhysicalMatching.H7StandaloneSmearedWardMatrixExpansion
