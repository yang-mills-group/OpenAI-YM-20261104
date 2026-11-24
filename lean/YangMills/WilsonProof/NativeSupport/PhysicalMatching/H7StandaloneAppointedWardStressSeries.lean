import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7StandaloneAppointedWardCoordinateSalary
import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7StandaloneWardColumnLaws
import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7StandalonePublicWardExistence
import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7StandaloneWardTensorPolynomial
import YM.Integration.WilsonMSbarStandaloneCorrelation

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace PhysicalMatching.H7StandaloneAppointedWardStressSeries
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


open PhysicalMatching.H7StandaloneWardTensorPolynomial
def selected (Z : WilsonPrescription g.core) (Q : Perspective H Z true)
    (pupils : Pupils) (B : Matrix4) :
    YangMills.Matching.WardStress.Series (YangMills.maxwellReference g) :=
  H7StandaloneWardTensorPolynomial.tensor H B
    (matrixCoefficients Z Q pupils) (rhsCoefficients Z Q pupils)

theorem sizeAtHeat (V : Vision E ξ) (Z : WilsonPrescription g.core) (Q : Perspective H Z true)
    (shapes : ReferenceShape Z V Q) (phase : Option (wardHierarchy V).Character)
    (o : YangMills.Spacetime) (pupils : Pupils) (B : Matrix4) (u : ℝ → Coords)
    (left : ∀ x, act B (act (matrixCoefficients Z Q pupils 0) x) = x)
    (right : ∀ x, act (matrixCoefficients Z Q pupils 0) (act B x) = x)
    (positive : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < ElectedMeasurement.clock V Z r)
    (shrinks : Tendsto (ElectedMeasurement.clock V Z) (𝓝[>] 0) (𝓝 0))
    (fourth : ∀ k : ℕ, Tendsto (fun r : ℝ => r^4 / (ElectedMeasurement.clock V Z r)^k)
      (𝓝[>] 0) (𝓝 0))
    (span : ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ a b, measuredStress V Z r a b =
        ∑ i, u r i • columns H a b i) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ r : ℝ in 𝓝[>] 0,
      size (u r - crop (ElectedMeasurement.clock V Z r : ℂ) N
        (coefficients B (matrixCoefficients Z Q pupils) (rhsCoefficients Z Q pupils))) ≤
        C * ‖(ElectedMeasurement.clock V Z r : ℂ)‖^(N+1) := by
  obtain ⟨C,hC,h⟩ := H7StandaloneAppointedWardCoordinateSalary.original
    V Z Q shapes phase o pupils B u left right span positive shrinks fourth N
  refine ⟨4*C, mul_nonneg (by norm_num) hC, ?_⟩
  filter_upwards [h] with r hr
  rw [H7StandaloneAppointedWardCoordinateSalary.cropFin]
  calc
    _ ≤ ∑ _i : Fin 4, C * |ElectedMeasurement.clock V Z r|^(N+1) := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hr i
    _ = _ := by
      simp [Finset.sum_const, nsmul_eq_mul, Complex.norm_real, Real.norm_eq_abs]
      ring

theorem determined (V : Vision E ξ) (Z : WilsonPrescription g.core) (Q : Perspective H Z true)
    (shapes : ReferenceShape Z V Q) (phase : Option (wardHierarchy V).Character)
    (o : YangMills.Spacetime) (pupils : Pupils) (B : Matrix4) (u : ℝ → Coords)
    (left : ∀ x, act B (act (matrixCoefficients Z Q pupils 0) x) = x)
    (right : ∀ x, act (matrixCoefficients Z Q pupils 0) (act B x) = x)
    (positive : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < ElectedMeasurement.clock V Z r)
    (shrinks : Tendsto (ElectedMeasurement.clock V Z) (𝓝[>] 0) (𝓝 0))
    (fourth : ∀ k : ℕ, Tendsto (fun r : ℝ => r^4 / (ElectedMeasurement.clock V Z r)^k)
      (𝓝[>] 0) (𝓝 0))
    (span : ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ a b, measuredStress V Z r a b =
        ∑ i, u r i • columns H a b i)
    (ground : rhsCoefficients Z Q pupils 0 = act (matrixCoefficients Z Q pupils 0) ![0,0,0,1])
    (M : YangMills.MSbar.Coefficients (YangMills.maxwellReference g))
    (S : YangMills.Matching.Conversion (YangMills.maxwellReference g))
    (read : ∀ (n : ℕ) (d : Caps n) (v : FVA2.GradedFar.Inputs g.core d) (k : ℕ)
      (x : YangMills.Points n), x ∈ conf n → S.correlation M k (publicLetters d v) x =
        groupCoefficient Z Q d v k x) :
    YangMills.Matching.WardStress.Determined M S (selected Z Q pupils B) := by
  let U := coefficients B (matrixCoefficients Z Q pupils) (rhsCoefficients Z Q pupils)
  have small : ∀ᶠ r : ℝ in 𝓝[>] 0, |ElectedMeasurement.clock V Z r| ≤ 1 := by
    filter_upwards [shrinks.eventually (Ioo_mem_nhds (by norm_num : (-1:ℝ)<0)
      (by norm_num : (0:ℝ)<1))] with r hr
    exact abs_le.mpr ⟨le_of_lt hr.1,le_of_lt hr.2⟩
  exact H7StandaloneInsertedPhysicalWardTests.determinedOnFiledCoordinates V Z Q shapes phase o
    M S (selected Z Q pupils B) u U (fun _ _ _ => rfl)
    (H7StandaloneAppointedWardCoordinateSalary.leading B _ _ left ground)
    (fun k i j => H7StandaloneWardColumnLaws.symmetric H (U k) i j)
    (fun k σ sign L hs hu i j => H7StandaloneWardColumnLaws.signedAxes H (U k) σ sign L hs hu i j)
    read span small shrinks fourth
    (H7StandaloneAppointedWardCoordinateSalary.original V Z Q shapes phase o pupils B u
      left right span positive shrinks fourth)

theorem namedOnMeasuredFrame (V : Vision E ξ) (Z : WilsonPrescription g.core)
    (M : YangMills.Matching.CorrelationOnly.Measurement (YangMills.maxwellReference g)
      (YangMills.hierarchy V.pupil.last V.pupil.P))
    (sameFrame : ∀ r, M.frame r 4 = YM.Answer.ContinuumLimit.ElectedMeasurement.frame V Z r 4)
    (clockZero : Tendsto M.clock (𝓝[>] 0) (𝓝 0))
    (clockPositive : ∀ᶠ r in 𝓝[>] (0:ℝ), 0 < M.clock r)
    (B : Matrix4) (L : ℕ → Matrix4) (rhs : ℕ → Coords)
    (prices : ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ r in 𝓝[>] (0:ℝ), ∃ u : Coords,
      (∀ a b, measuredStress V Z r a b = assembled H a b u) ∧
      size (u-crop (M.clock r : ℂ) N (coefficients B L rhs)) ≤
        C * ‖(M.clock r : ℂ)‖^(N+1)) :
    YangMills.Matching.CorrelationOnly.namedStress M (tensor H B L rhs) := by
  intro a b N out
  obtain ⟨C,hC,hprice⟩ := prices N
  let salary := C * dualCost H a b out
  have boundZero : Tendsto (fun r : ℝ => salary * |M.clock r|) (𝓝[>] 0) (𝓝 0) := by
    simpa using (tendsto_const_nhds (x:=salary)).mul clockZero.abs
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hprice, clockPositive, (tendsto_order.1 boundZero).2 ε hε] with r hu hr hεr
  obtain ⟨u,hphysical,hpaid⟩ := hu
  have h := H7StandaloneWardTensorPolynomial.atMeasured V Z B L rhs r (M.clock r : ℂ) N u C hphysical hpaid a b out
  have hp : 0 < ‖(M.clock r : ℂ)‖^N := pow_pos (norm_pos_iff.mpr (by exact_mod_cast hr.ne')) N
  have hdiv : ‖(out (measuredStress V Z r a b) -
      ∑ n : Fin (N+1), (M.clock r : ℂ)^n.val * out (tensor H B L rhs n.val a b)) /
      (M.clock r : ℂ)^N‖ ≤ salary * |M.clock r| := by
    rw [norm_div, norm_pow, div_le_iff₀ hp]
    simpa [salary, pow_succ, Complex.norm_real, Real.norm_eq_abs, mul_assoc,
      mul_left_comm, mul_comm] using h
  rw [dist_zero_right, sameFrame]
  exact hdiv.trans_lt hεr

theorem named (V : Vision E ξ) (Z : WilsonPrescription g.core) (Q : Perspective H Z true)
    (shapes : ReferenceShape Z V Q) (phase : Option (wardHierarchy V).Character)
    (o : YangMills.Spacetime) (pupils : Pupils) (B : Matrix4) (u : ℝ → Coords)
    (left : ∀ x, act B (act (matrixCoefficients Z Q pupils 0) x) = x)
    (right : ∀ x, act (matrixCoefficients Z Q pupils 0) (act B x) = x)
    (positive : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < ElectedMeasurement.clock V Z r)
    (shrinks : Tendsto (ElectedMeasurement.clock V Z) (𝓝[>] 0) (𝓝 0))
    (fourth : ∀ k : ℕ, Tendsto (fun r : ℝ => r^4 / (ElectedMeasurement.clock V Z r)^k)
      (𝓝[>] 0) (𝓝 0))
    (span : ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ a b, measuredStress V Z r a b =
        ∑ i, u r i • columns H a b i)
    (W : YangMills.Matching.CorrelationOnly.Measurement (YangMills.maxwellReference g)
      (YangMills.hierarchy V.pupil.last V.pupil.P))
    (frame : ∀ r, W.frame r 4 = ElectedMeasurement.frame V Z r 4)
    (clock : W.clock = ElectedMeasurement.clock V Z) :
    YangMills.Matching.CorrelationOnly.namedStress W (selected Z Q pupils B) := by
  apply namedOnMeasuredFrame V Z W frame (clock ▸ shrinks) (clock ▸ positive)
    B (matrixCoefficients Z Q pupils) (rhsCoefficients Z Q pupils)
  intro N
  obtain ⟨C,hC,h⟩ := sizeAtHeat V Z Q shapes phase o pupils B u left right positive
    shrinks fourth span N
  refine ⟨C,hC,?_⟩
  filter_upwards [h,span] with r hr hs
  exact ⟨u r,hs,by simpa only [clock] using hr⟩

theorem original (V : Vision E ξ) (Z : WilsonPrescription g.core) (Q : Perspective H Z true)
    (shapes : ReferenceShape Z V Q) (phase : Option (wardHierarchy V).Character)
    (o : YangMills.Spacetime) (pupils : Pupils) (B : Matrix4)
    (left : ∀ x, act B (act (matrixCoefficients Z Q pupils 0) x) = x)
    (right : ∀ x, act (matrixCoefficients Z Q pupils 0) (act B x) = x)
    (positive : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < ElectedMeasurement.clock V Z r)
    (shrinks : Tendsto (ElectedMeasurement.clock V Z) (𝓝[>] 0) (𝓝 0))
    (fourth : ∀ k : ℕ, Tendsto (fun r : ℝ => r^4 / (ElectedMeasurement.clock V Z r)^k)
      (𝓝[>] 0) (𝓝 0))
    (span : ∀ᶠ r : ℝ in 𝓝[>] 0, ∃ v : Coords, ∀ a b,
      measuredStress V Z r a b = ∑ i, v i • columns H a b i)
    (ground : rhsCoefficients Z Q pupils 0 = act (matrixCoefficients Z Q pupils 0) ![0,0,0,1])
    (M : YangMills.MSbar.Coefficients (YangMills.maxwellReference g))
    (S : YangMills.Matching.Conversion (YangMills.maxwellReference g))
    (read : ∀ (n : ℕ) (d : Caps n) (v : FVA2.GradedFar.Inputs g.core d) (k : ℕ)
      (x : YangMills.Points n), x ∈ conf n → S.correlation M k (publicLetters d v) x =
        groupCoefficient Z Q d v k x)
    (W : YangMills.Matching.CorrelationOnly.Measurement (YangMills.maxwellReference g)
      (YangMills.hierarchy V.pupil.last V.pupil.P))
    (frame : ∀ r, W.frame r 4 = ElectedMeasurement.frame V Z r 4)
    (clock : W.clock = ElectedMeasurement.clock V Z) :
    YangMills.Matching.WardStress.Determined M S (selected Z Q pupils B) ∧
      YangMills.Matching.CorrelationOnly.namedStress W (selected Z Q pupils B) := by
  classical
  let u (r : ℝ) : Coords := if h : ∃ v : Coords, ∀ a b,
      measuredStress V Z r a b = ∑ i, v i • columns H a b i then Classical.choose h else 0
  have hu : ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ a b,
      measuredStress V Z r a b = ∑ i, u r i • columns H a b i := by
    filter_upwards [span] with r hr
    simpa only [u, dif_pos hr] using Classical.choose_spec hr
  exact ⟨determined V Z Q shapes phase o pupils B u left right positive shrinks fourth hu ground M S read,
    named V Z Q shapes phase o pupils B u left right positive shrinks fourth hu W frame clock⟩

end PhysicalMatching.H7StandaloneAppointedWardStressSeries
end

