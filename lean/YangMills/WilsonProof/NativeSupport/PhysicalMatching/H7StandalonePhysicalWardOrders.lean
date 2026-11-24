import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7StandaloneInsertedPhysicalWardTests
import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7StandaloneWardCoefficientUniqueness

set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
namespace PhysicalMatching.H7StandaloneInsertedPhysicalWardTests
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


open PhysicalMatching.H7StandaloneSmearedWardMatrixExpansion


open PhysicalMatching.H7StandaloneIntegratedArbitraryWardSeries
open PhysicalMatching.H7StandaloneAppointedWardBalance
open PhysicalMatching.H7StandaloneSmearedConservation
open PhysicalMatching.H7StandaloneArbitraryWardTestReadings


open PhysicalMatching.H7StandaloneWardCoefficientUniqueness

theorem arbitraryPrependContinuous (n : ℕ) : Continuous (fun z : YangMills.Spacetime × YangMills.Points n => YangMills.Ward.prepend z.1 z.2) := by
  unfold YangMills.Ward.prepend
  apply (PiLp.continuous_toLp 2 (fun _ : Fin (n+1) => YangMills.Spacetime)).comp
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact continuous_fst
  · exact (PiLp.continuous_apply 2 (fun _ : Fin n => YangMills.Spacetime) j).comp continuous_snd

theorem readings {clock : ℝ → ℝ} {x : ℝ → ℂ} {c : ℕ → ℂ}
    (all : ∀ p, RowPrice clock p x c) :
    PhysicalMatching.H7StandaloneWardCoefficientUniqueness.Reading (𝓝[>] 0) clock x c := by
  intro p
  obtain ⟨C, hC, paid⟩ := all p
  refine ⟨C, hC, ?_⟩
  filter_upwards [paid] with r hr
  unfold PhysicalMatching.H7StandaloneWardCoefficientUniqueness.crop
  rw [← Fin.sum_univ_eq_sum_range (fun k : ℕ => (clock r : ℂ)^k * c k) (p+1)]
  exact hr

theorem exactSignedCoefficients {clock : ℝ → ℝ}
    (positive : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < clock r)
    (shrinks : Tendsto clock (𝓝[>] 0) (𝓝 0))
    {x y : ℝ → ℂ} {a b : ℕ → ℂ}
    (left : ∀ p, RowPrice clock p x a) (right : ∀ p, RowPrice clock p y b)
    (law : x =ᶠ[𝓝[>] 0] y) : ∀ k, a k = b k :=
  PhysicalMatching.H7StandaloneWardCoefficientUniqueness.throughResidual positive shrinks
    (readings left) (readings right)
    (PhysicalMatching.H7StandaloneWardCoefficientUniqueness.exactResidual clock law)

theorem uncenteredVacuumCoefficients {clock : ℝ → ℝ}
    (positive : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < clock r)
    (shrinks : Tendsto clock (𝓝[>] 0) (𝓝 0))
    (fourth : ∀ m : ℕ, Tendsto (fun r : ℝ => r^4 / (clock r)^m) (𝓝[>] 0) (𝓝 0))
    {x : ℝ → ℂ} {a : ℕ → ℂ} (paid : ∀ p, RowPrice clock p x a) (v : ℂ)
    (law : ∀ᶠ r in 𝓝[>] (0 : ℝ), x r = (r^4 : ℂ) * v) : ∀ k, a k = 0 := by
  apply PhysicalMatching.H7StandaloneWardCoefficientUniqueness.throughResidual positive shrinks
    (readings paid) (readings (fun _ => zeroPrice _ _))
  intro p
  refine ⟨‖v‖, norm_nonneg _, ?_⟩
  filter_upwards [law, positive, self_mem_nhdsWithin,
    (fourth (p+1)).eventually (gt_mem_nhds (zero_lt_one : (0:ℝ)<1))]
    with r hx ht hr hs
  have hr0 : 0 ≤ r := le_of_lt hr
  have hpow : r^4 ≤ |clock r|^(p+1) := by
    rw [abs_of_pos ht]
    exact ((div_lt_one (pow_pos ht _)).mp hs).le
  simpa only [hx, sub_zero, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hr0, mul_comm] using
      mul_le_mul_of_nonneg_right hpow (norm_nonneg v)

theorem finiteIntegratedTest {α ι : Type*} [MeasureSpace α]
    [Fintype ι] (w : α → ℂ) (a : ι → α → ℂ)
    (paid : ∀ i, Integrable (fun x : α => w x * a i x) (volume : Measure α)) :
    Integrable (fun x => w x * ∑ i, a i x) ∧
    (∫ x, w x * ∑ i, a i x) = ∑ i, ∫ x, w x * a i x := by
  simp only [Finset.mul_sum]
  exact ⟨integrable_finsetSum _ fun i _ => paid i,
    integral_finsetSum _ fun i _ => paid i⟩

theorem filedStressField (V : Vision E ξ) (a b : YM.Axis) :
    (wardHierarchy V).stress a b = V.pupil.last.sector.energy a b := rfl

/-- The grade-four physical measurement expressed in the published hierarchy's own complex action. -/
theorem filedStressFrame (V : Vision E ξ) (Z : WilsonPrescription g.core)
    (r : ℝ) (a b : YM.Axis) :
    ElectedMeasurement.frame V Z r 4 (measuredStress V Z r a b) =
      (r ^ 4 : ℂ) • (wardHierarchy V).stress a b := by
  first
  | exact frameReconstruction V Z r a b
  | with_unfolding_all exact frameReconstruction V Z r a b
  | simpa [wardHierarchy, YangMills.hierarchy] using frameReconstruction V Z r a b


theorem conservationAtEveryOrder (V : Vision E ξ) (Z : WilsonPrescription g.core)
    (Q : Perspective H Z true) (shapes : ReferenceShape Z V Q)
    (phase : Option (wardHierarchy V).Character) (o : YangMills.Spacetime)
    {n : ℕ} (d : Caps n) (v : FVA2.GradedFar.Inputs g.core d) (b : YM.Axis)
    (φ : YangMills.WilsonFamily.SeparatedTest (n+1))
    (u : ℝ → Fin 4 → ℂ) (U : ℕ → Fin 4 → ℂ)
    (real : ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ a b, measuredStress V Z r a b =
      ∑ i, u r i • columns H a b i)
    (small : ∀ᶠ r in 𝓝[>] (0 : ℝ), |ElectedMeasurement.clock V Z r| ≤ 1)
    (shrinks : Tendsto (ElectedMeasurement.clock V Z) (𝓝[>] 0) (𝓝 0))
    (paid : ∀ p, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ i,
      ‖u r i - ∑ j : Fin (p+1), (ElectedMeasurement.clock V Z r : ℂ)^j.val * U j.val i‖
        ≤ C * |ElectedMeasurement.clock V Z r|^(p+1)) :
    ∀ k, (∑ a : YM.Axis, ∑ j : Fin (k+1), formal Z Q d v
      (YangMills.Ward.firstDerivative a (fun x => φ x)) (fun x => x)
      (∑ i, U j.val i • columns H a b i) (k-j.val)) = 0 := by
  let w (a : YM.Axis) := YangMills.Ward.firstDerivative a (fun x => φ x)
  have ht a := (derivativeWeight φ a)
  have price (a : YM.Axis) (p : ℕ) := insertedPrice V Z Q shapes phase o d v (w a)
    (ht a).1 (ht a).2.1 (fun x => x) continuous_id
    (fun z hz => (ht a).2.2 hz) a b u U
    (real.mono fun r h => h a b) small paid p
  have law : (fun r => ∑ a : YM.Axis, occupied V Z phase o d v (w a) (fun x => x)
      (measuredStress V Z r a b) r) =ᶠ[𝓝[>] 0] (fun _ => (0:ℂ)) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    have h := PhysicalMatching.H7StandaloneArbitraryWardTestReadings.conservationTest
      V phase r hr o (ElectedMeasurement.inputs V Z r d v) b φ
    simpa only [occupied, filedStressFrame, PhysicalMatching.H7StandaloneFourSmearedWardReadings.marked, w] using h
  exact exactSignedCoefficients (ElectedMeasurement.positive V Z Q) shrinks
    (fun p => sumPrice (fun a => price a p)) (fun p => zeroPrice _ p) law


theorem coefficientIntegrableAtCap {α : Type*} [NormedAddCommGroup α] [NormedSpace ℝ α]
    [FiniteDimensional ℝ α] [MeasureSpace α] [BorelSpace α]
    [IsLocallyFiniteMeasure (volume : Measure α)] (V : Vision E ξ) (Z : WilsonPrescription g.core)
    (Q : Perspective H Z true) (shapes : ReferenceShape Z V Q)
    (phase : Option (wardHierarchy V).Character) (o : E4) (p : ℕ) {n : ℕ}
    (cap : ℕ) (d : Caps n) (within : ∀ i, d i ≤ cap) (v : FVA2.GradedFar.Inputs g.core d)
    (w : α → ℂ) (hw : Continuous w) (hc : HasCompactSupport w) (sh : α → YangMills.Points n)
    (hs : Continuous sh) (clear : ∀ z ∈ tsupport w, sh z ∈ conf n) :
    Integrable (fun z => w z * groupCoefficient Z Q d v p (sh z)) := by
  let K := sh '' tsupport w
  have hK : IsCompact K := hc.image hs
  have sep : K ⊆ conf n := by rintro _ ⟨z,hz,rfl⟩; exact clear z hz
  have crops := filedCrops V Z Q shapes cap d within v phase o
  have ib (k : ℕ) : Integrable (fun z => w z * groupCoefficient Z Q d v k (sh z)) :=
    weightedIntegrable w hw hc sh hs _ (coefficientContinuousOn (ElectedMeasurement.positive V Z Q) crops K hK sep k)
  exact ib p

theorem coefficientIntegrableOnEveryFiledGrade {α : Type*} [NormedAddCommGroup α] [NormedSpace ℝ α]
    [FiniteDimensional ℝ α] [MeasureSpace α] [BorelSpace α]
    [IsLocallyFiniteMeasure (volume : Measure α)] (V : Vision E ξ) (Z : WilsonPrescription g.core)
    (Q : Perspective H Z true) (shapes : ReferenceShape Z V Q)
    (phase : Option (wardHierarchy V).Character) (o : E4) (p : ℕ) {n : ℕ}
    (d : Caps n) (v : FVA2.GradedFar.Inputs g.core d)
    (w : α → ℂ) (hw : Continuous w) (hc : HasCompactSupport w) (sh : α → YangMills.Points n)
    (hs : Continuous sh) (clear : ∀ z ∈ tsupport w, sh z ∈ conf n) :
    Integrable (fun z => w z * groupCoefficient Z Q d v p (sh z)) := by
  classical
  let cap := max 4 (Finset.univ.sup d)
  have within (i : Fin n) : d i ≤ cap :=
    (Finset.le_sup (f := d) (Finset.mem_univ i)).trans (le_max_right _ _)
  exact coefficientIntegrableAtCap V Z Q shapes phase o p cap d within v w hw hc sh hs clear

private theorem rangeIic (p : ℕ) : Finset.range (p+1) = Finset.Iic p := by
  ext i
  simp

private theorem finIic (p : ℕ) (f : ℕ → ℂ) :
    (∑ i : Fin (p+1), f i.val) = ∑ i ∈ Finset.Iic p, f i := by
  rw [Fin.sum_univ_eq_sum_range, rangeIic]


open PhysicalMatching.H7StandaloneArbitraryWardTestReadings
open PhysicalMatching.H7StandaloneVacuumWardReading

theorem integratedFiledInsertion {α : Type*} [NormedAddCommGroup α] [NormedSpace ℝ α]
    [FiniteDimensional ℝ α] [MeasureSpace α] [BorelSpace α]
    [IsLocallyFiniteMeasure (volume : Measure α)] (V : Vision E ξ) (Z : WilsonPrescription g.core)
    (Q : Perspective H Z true) (shapes : ReferenceShape Z V Q)
    (phase : Option (wardHierarchy V).Character) (o : E4) {n : ℕ}
    (d : Caps n) (v : FVA2.GradedFar.Inputs g.core d) (w : α → ℂ)
    (hw : Continuous w) (hc : HasCompactSupport w) (sh : α → YangMills.Points (n+1))
    (hs : Continuous sh) (clear : ∀ z ∈ tsupport w, sh z ∈ conf (n+1))
    (f : ℕ → (YangMills.maxwellReference g).sector 4) (k : ℕ) :
    let coeff (j : Fin (k+1)) (z : α) := groupCoefficient Z Q (Fin.cons 4 d)
      (insertedLabels d v (f j.val)) (k-j.val) (sh z)
    Integrable (fun z => w z * ∑ j, coeff j z) ∧
      (∫ z, w z * ∑ j, coeff j z) = ∑ j : Fin (k+1), formal Z Q d v w sh (f j.val) (k-j.val) := by
  apply finiteIntegratedTest
  intro j
  exact coefficientIntegrableOnEveryFiledGrade V Z Q shapes phase o (k-j.val)
    (Fin.cons 4 d) (insertedLabels d v (f j.val)) w hw hc sh hs clear

theorem vacuumAtEveryOrder (V : Vision E ξ) (Z : WilsonPrescription g.core)
    (Q : Perspective H Z true) (shapes : ReferenceShape Z V Q)
    (phase : Option (wardHierarchy V).Character) (o : E4) (φ : YangMills.WilsonFamily.SeparatedTest 1) (a b : YM.Axis)
    (u : ℝ → Fin 4 → ℂ) (U : ℕ → Fin 4 → ℂ)
    (real : ∀ᶠ r in 𝓝[>] (0:ℝ), measuredStress V Z r a b = ∑ i, u r i • columns H a b i)
    (small : ∀ᶠ r in 𝓝[>] (0:ℝ), |ElectedMeasurement.clock V Z r| ≤ 1)
    (shrinks : Tendsto (ElectedMeasurement.clock V Z) (𝓝[>] 0) (𝓝 0))
    (fourth : ∀ m : ℕ, Tendsto (fun r : ℝ => r^4 / (ElectedMeasurement.clock V Z r)^m)
      (𝓝[>] 0) (𝓝 0))
    (paid : ∀ p, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ i,
      ‖u r i - ∑ j : Fin (p+1), (ElectedMeasurement.clock V Z r : ℂ)^j.val * U j.val i‖
        ≤ C * |ElectedMeasurement.clock V Z r|^(p+1)) :
    ∀ k, (∑ j : Fin (k+1), formal Z Q (fun i : Fin 0 => Fin.elim0 i)
      (fun i : Fin 0 => Fin.elim0 i) (fun z => φ z) id
      (∑ i, U j.val i • columns H a b i) (k-j.val)) = 0 := by
  let d : Caps 0 := fun i => Fin.elim0 i
  let v : FVA2.GradedFar.Inputs g.core d := fun i => Fin.elim0 i
  have hz r : ElectedMeasurement.inputs V Z r d v = emptyTail V := funext fun i => Fin.elim0 i
  have price p := insertedPrice V Z Q shapes phase o d v (fun z => φ z)
    φ.continuous φ.hasCompactSupport id continuous_id (fun x hx => φ.tsupport_subset hx)
    a b u U real small paid p
  apply uncenteredVacuumCoefficients (ElectedMeasurement.positive V Z Q) shrinks fourth price
    ((∫ x : YangMills.Points 1, φ x) * atOrigin V phase ((wardHierarchy V).stress a b))
  exact Filter.Eventually.of_forall fun r => by
    simpa only [occupied,filedStressFrame,hz,id_eq] using vacuumTest V phase r o φ a b

theorem translationAtEveryOrder (V : Vision E ξ) (Z : WilsonPrescription g.core)
    (Q : Perspective H Z true) (shapes : ReferenceShape Z V Q)
    (phase : Option (wardHierarchy V).Character) (o : E4) {n : ℕ}
    (d : Caps (n+1)) (v : FVA2.GradedFar.Inputs g.core d) (b : YM.Axis)
    (P : PhysicalMatching.H7StandaloneArbitraryWardTestReadings.Shell n)
    (u : ℝ → Fin 4 → ℂ) (U : ℕ → Fin 4 → ℂ)
    (real : ∀ᶠ r in 𝓝[>] (0:ℝ), ∀ a b, measuredStress V Z r a b = ∑ i, u r i • columns H a b i)
    (small : ∀ᶠ r in 𝓝[>] (0:ℝ), |ElectedMeasurement.clock V Z r| ≤ 1)
    (shrinks : Tendsto (ElectedMeasurement.clock V Z) (𝓝[>] 0) (𝓝 0))
    (paid : ∀ p, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ i,
      ‖u r i - ∑ j : Fin (p+1), (ElectedMeasurement.clock V Z r : ℂ)^j.val * U j.val i‖
        ≤ C * |ElectedMeasurement.clock V Z r|^(p+1)) :
    ∀ k, -(∑ a : YM.Axis, ∑ j : Fin (k+1), formal Z Q d v
      (PhysicalMatching.H7StandaloneArbitraryWardTestReadings.weight P a)
      (fun z : YangMills.Spacetime × YangMills.Points (n+1) => YangMills.Ward.prepend z.1 z.2)
      (∑ i, U j.val i • columns H a b i) (k-j.val)) =
      -(∫ x : YangMills.Points (n+1), YangMills.Ward.firstDerivative b (fun y => P.translation y) x *
        groupCoefficient Z Q d v k x) := by
  let w := PhysicalMatching.H7StandaloneArbitraryWardTestReadings.weight P
  let sh (z : YangMills.Spacetime × YangMills.Points (n+1)) := YangMills.Ward.prepend z.1 z.2
  have hsh : Continuous sh := by exact arbitraryPrependContinuous _
  have price (a : YM.Axis) (p : ℕ) := insertedPrice V Z Q shapes phase o d v (w a)
    (PhysicalMatching.H7StandaloneArbitraryWardTestReadings.smoothWeight P a)
    (PhysicalMatching.H7StandaloneArbitraryWardTestReadings.compact P a) sh hsh
    (fun z hz => PhysicalMatching.H7StandaloneArbitraryWardTestReadings.separated P a hz)
    a b u U (real.mono fun r h => h a b) small paid p
  have hδ := derivativeWeight P.translation b
  have right p := integralOnEveryFiledGrade V Z Q shapes phase o p d v
    (YangMills.Ward.firstDerivative b (fun y => P.translation y)) hδ.1 hδ.2.1
    id continuous_id (fun x hx => hδ.2.2 hx)
  let dt : Caps n := fun i => d i.succ
  let vt : FVA2.GradedFar.Inputs g.core dt := fun i => v i.succ
  have head r : ElectedMeasurement.inputs V Z r d v =
      Fin.cons ⟨d 0,ElectedMeasurement.frame V Z r (d 0) (v 0)⟩
        (ElectedMeasurement.inputs V Z r dt vt) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  have law : (fun r => -(∑ a : YM.Axis, occupied V Z phase o d v (w a) sh
        (measuredStress V Z r a b) r)) =ᶠ[𝓝[>] (0:ℝ)] (fun r =>
        -(∫ x : YangMills.Points (n+1), YangMills.Ward.firstDerivative b (fun y => P.translation y) x *
          (wardHierarchy V).correlation phase (ElectedMeasurement.inputs V Z r d v) (sites r o x))) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    have h := translationTest V phase (ElectedMeasurement.frame V Z r (d 0) (v 0))
      (ElectedMeasurement.inputs V Z r dt vt) r hr o P b
    have pvol : (volume : Measure (YangMills.Spacetime × YangMills.Points (n+1))) =
        (volume : Measure YangMills.Spacetime).prod (volume : Measure (YangMills.Points (n+1))) := rfl
    first
    | simpa only [occupied,filedStressFrame,head,w,sh,pvol,
      PhysicalMatching.H7StandaloneArbitraryWardTestReadings.weight,
      PhysicalMatching.H7StandaloneArbitraryWardTestReadings.density,mul_assoc,id_eq] using h
    | with_unfolding_all simpa only [occupied,filedStressFrame,head,w,sh,pvol,
        PhysicalMatching.H7StandaloneArbitraryWardTestReadings.weight,
        PhysicalMatching.H7StandaloneArbitraryWardTestReadings.density,mul_assoc,id_eq] using h
  exact exactSignedCoefficients (ElectedMeasurement.positive V Z Q) shrinks
    (fun p => negPrice (sumPrice (fun a => price a p))) (fun p => negPrice (right p)) law

end PhysicalMatching.H7StandaloneInsertedPhysicalWardTests

