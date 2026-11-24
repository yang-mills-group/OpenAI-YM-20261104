import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7StandaloneFourWardBalance
import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7StandaloneSmearedWardMatrixExpansion
import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7StandaloneWardSeriesDivision

namespace PhysicalMatching.H7StandaloneAppointedWardCoordinateSalary
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
open scoped BigOperators Classical Topology


open PhysicalMatching.H7StandaloneFiniteWardMatrix PhysicalMatching.H7StandaloneFiledWardMatrixCoefficients
open PhysicalMatching.H7StandaloneWardSeriesDivision
open YM.Integration.WilsonGraphPublishedShapeEstimate

theorem cropFin {X : Type*} [AddCommMonoid X] [Module ℂ X] (t : ℂ) (p : ℕ) (f : ℕ → X) :
    crop t p f = ∑ k : Fin (p+1), t^k.val • f k.val := by
  have h : Finset.Iic p = Finset.range (p+1) := by ext i; simp
  unfold crop
  rw [h]
  exact (Fin.sum_univ_eq_sum_range (fun k : ℕ => t^k • f k) (p+1)).symm

theorem perturbation (V : Vision E ξ) (Z : WilsonPrescription g.core) (Q : Perspective H Z true)
    (shapes : ReferenceShape Z V Q) (phase : Option (wardHierarchy V).Character)
    (o : YangMills.Spacetime) (P : Pupils) (B : Matrix4)
    (shrinks : Tendsto (ElectedMeasurement.clock V Z) (𝓝[>] 0) (𝓝 0)) :
    ∀ᶠ r : ℝ in 𝓝[>] 0,
      matrixSize B * matrixSize (matrixCoefficients Z Q P 0 - matrix V Z phase r o P) ≤ 1/2 := by
  obtain ⟨C,D,hC,hD,prices⟩ := H7StandaloneSmearedWardMatrixExpansion.original V Z Q shapes phase o 0 P
  have ha : Tendsto (fun r : ℝ => |ElectedMeasurement.clock V Z r|) (𝓝[>] 0) (𝓝 0) := by
    simpa using shrinks.abs
  have hs : Tendsto (fun r : ℝ => matrixSize B*(C*|ElectedMeasurement.clock V Z r|)) (𝓝[>] 0) (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := matrixSize B)).mul ((tendsto_const_nhds (x := C)).mul ha)
  filter_upwards [prices, (tendsto_order.1 hs).2 (1/2) (by norm_num)] with r hr hsmall
  have he : matrixSize (matrix V Z phase r o P - matrixCoefficients Z Q P 0) ≤
      C*|ElectedMeasurement.clock V Z r| := by simpa using hr.1
  have flip : matrixCoefficients Z Q P 0 - matrix V Z phase r o P =
      -(matrix V Z phase r o P - matrixCoefficients Z Q P 0) := by abel
  have negSize (M : Matrix4) : matrixSize (-M) = matrixSize M := by
    change (∑ i : Fin 4, ∑ j : Fin 4, ‖-(M i j)‖) = ∑ i : Fin 4, ∑ j : Fin 4, ‖M i j‖
    simp only [norm_neg]
  rw [flip, negSize]
  exact (mul_le_mul_of_nonneg_left he (matrixSize_nonneg B)).trans hsmall.le

theorem uncenteredPrice (V : Vision E ξ) (Z : WilsonPrescription g.core)
    (phase : Option (wardHierarchy V).Character) (o : YangMills.Spacetime) (P : Pupils)
    (u : ℝ → Coords)
    (span : ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ a b, measuredStress V Z r a b = ∑ i, u r i • columns H a b i)
    (positive : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < ElectedMeasurement.clock V Z r)
    (fourth : ∀ k : ℕ, Tendsto (fun r : ℝ => r^4 / (ElectedMeasurement.clock V Z r)^k)
      (𝓝[>] 0) (𝓝 0)) (p : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ r : ℝ in 𝓝[>] 0,
      size (act (matrix V Z phase r o P) (u r) - rightSide V Z phase r o P) ≤
        K*|ElectedMeasurement.clock V Z r|^(p+1) := by
  let v := (∫ x : YangMills.Points 1, P.vacuum x) *
    H7StandaloneVacuumWardReading.atOrigin V phase ((wardHierarchy V).stress 0 0)
  refine ⟨‖v‖, norm_nonneg _, ?_⟩
  have hq := (tendsto_order.1 (fourth (p+1))).2 1 zero_lt_one
  filter_upwards [span, positive, self_mem_nhdsWithin, hq] with r hspan ht hr h
  have hr' : 0 < r := hr
  have scale : r^4 ≤ |ElectedMeasurement.clock V Z r|^(p+1) := by
    simpa [abs_of_pos ht] using ((div_lt_one (pow_pos ht (p+1))).1 h).le
  have bal := H7StandaloneFourWardBalance.original V Z phase r hr' o P (u r) hspan
  change size (H7StandaloneFiniteWardMatrix.act (matrix V Z phase r o P) (u r) - _) ≤ _
  rw [bal]
  have hp : size (![ (r^4 : ℂ) * v, 0, 0, 0] : Coords) = r^4 * ‖v‖ := by
    simp [size, Fin.sum_univ_succ, norm_mul, norm_pow, Real.norm_eq_abs, abs_of_pos hr']
  rw [hp, mul_comm]
  exact mul_le_mul_of_nonneg_left scale (norm_nonneg _)

theorem original (V : Vision E ξ) (Z : WilsonPrescription g.core) (Q : Perspective H Z true)
    (shapes : ReferenceShape Z V Q) (phase : Option (wardHierarchy V).Character)
    (o : YangMills.Spacetime) (P : Pupils) (B : Matrix4) (u : ℝ → Coords)
    (left : ∀ x, act B (act (matrixCoefficients Z Q P 0) x) = x)
    (right : ∀ x, act (matrixCoefficients Z Q P 0) (act B x) = x)
    (span : ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ a b, measuredStress V Z r a b = ∑ i, u r i • columns H a b i)
    (positive : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < ElectedMeasurement.clock V Z r)
    (shrinks : Tendsto (ElectedMeasurement.clock V Z) (𝓝[>] 0) (𝓝 0))
    (fourth : ∀ k : ℕ, Tendsto (fun r : ℝ => r^4 / (ElectedMeasurement.clock V Z r)^k)
      (𝓝[>] 0) (𝓝 0)) (p : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ i : Fin 4,
      ‖u r i - ∑ k : Fin (p+1), (ElectedMeasurement.clock V Z r : ℂ)^k.val *
        coefficients B (matrixCoefficients Z Q P) (rhsCoefficients Z Q P) k.val i‖ ≤
        K * |ElectedMeasurement.clock V Z r|^(p+1) := by
  classical
  let L := matrixCoefficients Z Q P
  let b := rhsCoefficients Z Q P
  let U := coefficients B L b
  obtain ⟨C,D,hC,hD,prices⟩ := H7StandaloneSmearedWardMatrixExpansion.original V Z Q shapes phase o p P
  obtain ⟨E0,hE0,paid⟩ := uncenteredPrice V Z phase o P u span positive fourth p
  let K := 2 * matrixSize B * (E0 + D + C*(∑ k ∈ Finset.Iic p, size (U k)) +
    ∑ i ∈ Finset.Iic p, ∑ j ∈ Finset.Iic p, size (act (L i) (U j)))
  refine ⟨max 0 K, le_max_left _ _, ?_⟩
  have ha : Tendsto (fun r : ℝ => |ElectedMeasurement.clock V Z r|) (𝓝[>] 0) (𝓝 0) := by
    simpa using shrinks.abs
  filter_upwards [prices, paid, perturbation V Z Q shapes phase o P B shrinks,
    (tendsto_order.1 ha).2 1 zero_lt_one] with r hprices hpaid hpert heat
  let t := (ElectedMeasurement.clock V Z r : ℂ)
  have ht : ‖t‖ = |ElectedMeasurement.clock V Z r| := by simp [t, Real.norm_eq_abs]
  have entries : matrixSize (matrix V Z phase r o P - crop t p L) ≤ C * ‖t‖^(p+1) := by
    simpa [cropFin, ht, t, L, Real.norm_eq_abs] using hprices.1
  have rhs : size (rightSide V Z phase r o P - crop t p b) ≤ D * ‖t‖^(p+1) := by
    simpa [cropFin, ht, t, b, Real.norm_eq_abs] using hprices.2
  have hrow : size (act (matrix V Z phase r o P) (u r) - rightSide V Z phase r o P) ≤ E0 * ‖t‖^(p+1) := by
    simpa only [ht] using hpaid
  have bound := H7StandaloneWardSeriesDivision.original t p (matrix V Z phase r o P) B L b
    (u r) (rightSide V Z phase r o P) C D E0 left right hpert (ht.trans_le heat.le) entries rhs hrow
  intro i
  have h := (coordinate_le (u r - crop t p U) i).trans bound
  have normPrice : ‖u r i - ∑ k : Fin (p+1), t^k.val * U k.val i‖ ≤ K * |ElectedMeasurement.clock V Z r|^(p+1) := by
    simpa [cropFin, K, U, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ht] using h
  exact normPrice.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg (abs_nonneg _) _))

theorem leading (B : Matrix4) (L : ℕ → Matrix4) (b : ℕ → Coords)
    (left : ∀ u, act B (act (L 0) u) = u) (ground : b 0 = act (L 0) ![0,0,0,1]) :
    coefficients B L b 0 = ![0,0,0,1] := by rw [groundCoefficient, ground, left]

end PhysicalMatching.H7StandaloneAppointedWardCoordinateSalary
