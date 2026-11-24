import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7StandaloneWardSeriesDivision
import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7StandaloneAppointedPublicWardRows
import YangMills.WilsonProof.NativeSupport.WardStressSeries

set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
namespace PhysicalMatching.H7StandaloneWardTensorPolynomial
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
open PhysicalMatching.H7StandaloneFiniteWardMatrix
open PhysicalMatching.H7StandaloneWardSeriesDivision

/-- The four fixed Maxwell fields are selected before the measured publication. -/
def assembled (hg : g.core.Simple) (a b : YM.Axis) (u : Coords) :
    (YangMills.maxwellReference g).sector 4 :=
  ∑ k : Fin 4, u k • columns hg a b k

def tensor (hg : g.core.Simple) (B : Matrix4) (L : ℕ → Matrix4) (rhs : ℕ → Coords) :
    YangMills.Matching.WardStress.Series (YangMills.maxwellReference g) :=
  fun n a b => assembled hg a b (coefficients B L rhs n)

theorem dual (hg : g.core.Simple) (a b : YM.Axis) (u : Coords)
    (out : (YangMills.maxwellReference g).sector 4 →ₗ[ℂ] ℂ) :
    out (assembled hg a b u) = ∑ k : Fin 4, u k * out (columns hg a b k) := by
  simp [assembled, smul_eq_mul]

theorem assembled_sub (hg : g.core.Simple) (a b : YM.Axis) (u v : Coords) :
    assembled hg a b (u-v) = assembled hg a b u - assembled hg a b v := by
  unfold assembled
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  exact sub_smul (u k) (v k) (columns hg a b k)

theorem polynomial (hg : g.core.Simple) (B : Matrix4) (L : ℕ → Matrix4)
    (rhs : ℕ → Coords) (a b : YM.Axis) (w : ℂ) (N : ℕ) :
    assembled hg a b (crop w N (coefficients B L rhs)) =
      ∑ n : Fin (N+1), w^n.val • tensor hg B L rhs n.val a b := by
  classical
  have hindex : Finset.Iic N = Finset.range (N+1) := by ext m; simp
  have hf : (∑ n : Fin (N+1), w^n.val • tensor hg B L rhs n.val a b) =
      ∑ n ∈ Finset.range (N+1), w^n • tensor hg B L rhs n a b :=
    Fin.sum_univ_eq_sum_range (fun n : ℕ => w^n • tensor hg B L rhs n a b) (N+1)
  rw [hf]
  unfold crop tensor assembled
  rw [hindex]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_smul,
    Finset.smul_sum, mul_smul]
  exact Finset.sum_comm

def dualCost (hg : g.core.Simple) (a b : YM.Axis)
    (out : (YangMills.maxwellReference g).sector 4 →ₗ[ℂ] ℂ) : ℝ :=
  ∑ k : Fin 4, ‖out (columns hg a b k)‖

theorem dualCost_nonneg (hg : g.core.Simple) (a b : YM.Axis)
    (out : (YangMills.maxwellReference g).sector 4 →ₗ[ℂ] ℂ) :
    0 ≤ dualCost hg a b out := Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem dualPrice (hg : g.core.Simple) (a b : YM.Axis) (u : Coords)
    (out : (YangMills.maxwellReference g).sector 4 →ₗ[ℂ] ℂ) :
    ‖out (assembled hg a b u)‖ ≤ size u * dualCost hg a b out := by
  classical
  rw [dual]
  calc
    _ ≤ ∑ k : Fin 4, ‖u k * out (columns hg a b k)‖ := norm_sum_le _ _
    _ ≤ ∑ k : Fin 4, size u * ‖out (columns hg a b k)‖ := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (coordinate_le u k) (norm_nonneg _)
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem atMeasured (V : Vision E ξ) (Z : WilsonPrescription g.core)
    (B : Matrix4) (L : ℕ → Matrix4) (rhs : ℕ → Coords)
    (r : ℝ) (w : ℂ) (N : ℕ) (u : Coords) (C : ℝ)
    (physical : ∀ a b, measuredStress V Z r a b = assembled H a b u)
    (price : size (u-crop w N (coefficients B L rhs)) ≤ C * ‖w‖^(N+1))
    (a b : YM.Axis) (out : (YangMills.maxwellReference g).sector 4 →ₗ[ℂ] ℂ) :
    ‖out (measuredStress V Z r a b) -
        ∑ n : Fin (N+1), w^n.val * out (tensor H B L rhs n.val a b)‖ ≤
      (C * dualCost H a b out) * ‖w‖^(N+1) := by
  have h := dualPrice H a b (u-crop w N (coefficients B L rhs)) out
  rw [assembled_sub, polynomial, map_sub, map_sum] at h
  simp only [map_smul, smul_eq_mul] at h
  rw [physical]
  calc
    _ ≤ _ := h
    _ ≤ (C*‖w‖^(N+1))*dualCost H a b out :=
      mul_le_mul_of_nonneg_right price (dualCost_nonneg H a b out)
    _ = _ := by ring

/-- One ground matrix and one formal right side precede every radius and every dual. -/
theorem original (V : Vision E ξ) (Z : WilsonPrescription g.core)
    (M : YangMills.Matching.Measurement (YangMills.maxwellReference g)
      (YangMills.hierarchy V.pupil.last V.pupil.P))
    (sameFrame : ∀ r, M.frame r 4 = YM.Answer.ContinuumLimit.ElectedMeasurement.frame V Z r 4)
    (clockZero : Tendsto M.clock (𝓝[>] 0) (𝓝 0))
    (clockPositive : ∀ᶠ r in 𝓝[>] (0:ℝ), 0 < M.clock r)
    (B : Matrix4) (L : ℕ → Matrix4) (rhs : ℕ → Coords)
    (prices : ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ r in 𝓝[>] (0:ℝ), ∃ u : Coords,
      (∀ a b, measuredStress V Z r a b = assembled H a b u) ∧
      size (u-crop (M.clock r : ℂ) N (coefficients B L rhs)) ≤
        C * ‖(M.clock r : ℂ)‖^(N+1)) :
    YangMills.Matching.WardStress.Named M (tensor H B L rhs) := by
  intro a b N out
  obtain ⟨C,hC,hprice⟩ := prices N
  let salary := C * dualCost H a b out
  have boundZero : Tendsto (fun r : ℝ => salary * |M.clock r|) (𝓝[>] 0) (𝓝 0) := by
    simpa using (tendsto_const_nhds (x:=salary)).mul clockZero.abs
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hprice, clockPositive, (tendsto_order.1 boundZero).2 ε hε] with r hu hr hεr
  obtain ⟨u,hphysical,hpaid⟩ := hu
  have h := atMeasured V Z B L rhs r (M.clock r : ℂ) N u C hphysical hpaid a b out
  have hp : 0 < ‖(M.clock r : ℂ)‖^N := pow_pos (norm_pos_iff.mpr (by exact_mod_cast hr.ne')) N
  have hdiv : ‖(out (measuredStress V Z r a b) -
      ∑ n : Fin (N+1), (M.clock r : ℂ)^n.val * out (tensor H B L rhs n.val a b)) /
      (M.clock r : ℂ)^N‖ ≤ salary * |M.clock r| := by
    rw [norm_div, norm_pow, div_le_iff₀ hp]
    simpa [salary, pow_succ, Complex.norm_real, Real.norm_eq_abs, mul_assoc,
      mul_left_comm, mul_comm] using h
  rw [dist_zero_right, sameFrame]
  exact hdiv.trans_lt hεr

end PhysicalMatching.H7StandaloneWardTensorPolynomial
