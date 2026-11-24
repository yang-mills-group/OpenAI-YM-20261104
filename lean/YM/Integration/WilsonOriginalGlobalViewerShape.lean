import YM.Integration.WilsonOriginalCompactPoseCover
import YM.Integration.WilsonOriginalUnchartedTensor
import YM.Integration.WilsonOriginalHomogeneousViewerShape
import YM.Integration.WilsonOriginalHomogeneousShapeTensor
import YM.Integration.WilsonOriginalAffineViewerJets
import YM.Integration.WilsonOriginalHomogeneousShapeWithdrawal
import YM.Integration.WilsonOriginalCartesianJetComponents
import YM.Integration.WilsonOriginalFiniteSpatialTensor
import YM.Integration.WilsonOriginalInteriorShapeValues
import YM.Integration.WilsonOriginalHomogeneousCompactInvoice
/-! The signed compact test on the elected homogeneous physical mean supplies
both inputs of the Fourier readback on its real box. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalGlobalViewerShape
open Filter Function Set Metric Lattice Wilson RG Source Extraction Table Spec
open PhysicalNext.Repeat.Legato RG17 Trace Trace.Pilot PhysMS Climb GapsContact
open OPE.Orbits (Reader)
open OPE OPE.Orbits.Reader Maxwell XSpace XSpace.Normalize FVA2 FVA2.Register
open WilsonPositionHomogeneousFrame WilsonMacroscopicRichTwoDatePivot WilsonViewerElectedHierarchy
open scoped Topology Classical BigOperators
universe u
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    {F : Final R.family f S} {Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin}
    {J : ℝ → PhysMS.tower S} {L : EveryPhase.Almanac F} {Y : (Bel R.family.book).Hierarchy}
    {arch : Trace.Terrace.Arch R.family} {ℓ : Ultrafilter (ℕ×ℕ)}
    {simple : G.Simple} {cohort : Ultrafilter (ℕ×ℕ) → Prop}
    (run : Selected.{u} F L Q J Y arch ℓ simple cohort) (Z : WilsonPrescription G)



open UnitAddTorus AddCircle
open WilsonOriginalFourierBoxIntegral (localize)
open WilsonOriginalFourierLattice (height)
open WilsonOriginalPhysicalBoxSlices (positions)

open scoped ContDiff
open MeasureTheory
open WilsonOriginalTestedFourierBank (Prices)
open WilsonOriginalIntegerModeCut (size size_pow)
open WilsonOriginalFourierBoxIntegral (test)

local notation "θ" => WilsonPositionHomogeneousFrame.reading F J Z
local notation "pub" => homogeneous F J Z


open WilsonOriginalCompactPoseCover (Box)

def Tested {n m : ℕ} (d : Fin n → ℕ) (v : MaxwellSlots R.family d)
    (coeff : ℕ → Points n → ℂ) (Dtest : Box n (m+1) → ℕ) : Prop := ∀ B : Box n (m+1), ∀ q : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ r in trail,
      ∀ φ : Fin (m+1) → ℝ → ℂ, (∀ i, ContDiff ℝ ∞ (φ i)) →
        (∀ i t, t ∉ Icc (1/6:ℝ) (5/6) → φ i t = 0) → ∀ A : ℝ, 0 ≤ A →
        (∀ o : Fin (m+1) → ℕ, (∀ i, o i ≤ Dtest B) → ∀ x : Fin (m+1) → ℝ,
          ‖∏ i, iteratedDeriv (o i) (φ i) (x i)‖ ≤ A) →
        ‖(∫ x, (∏ i,φ i (x i))*measured F none (pub r) v r (B.origin+B.axes x)) -
          ∑ k : Fin (q+1), (θ r:ℂ)^k.val*(∫ x, (∏ i,φ i (x i))*coeff k.val (B.origin+B.axes x))‖
             ≤ C*(θ r)^q*A

include run in
theorem original {n m : ℕ} (d : Fin n → ℕ) (v : MaxwellSlots R.family d)
    (clock : Coupling G θ) (coordinates : (Fin (m+1) → ℝ) ≃L[ℝ] Points n)
    (coeff : ℕ → Points n → ℂ) (smooth : ∀ k, ContDiffOn ℝ ∞ (coeff k) (conf n))
    (Dtest : Box n (m+1) → ℕ)
    (earned : Tested (F:=F) (J:=J) Z d v coeff Dtest)
    (K : Set (Points n)) (compact : IsCompact K) (separated : K ⊆ conf n)
    (p j : ℕ) {ε : ℝ} (eps : 0 < ε) :
    ∀ᶠ r in trail, ∀ x ∈ K, ∀ who : Viewers F,
      ‖iteratedFDeriv ℝ j (measured F who (pub r) v r) x -
        iteratedFDeriv ℝ j (fun z => ∑ k : Fin (p+1), (θ r:ℂ)^k.val*coeff k.val z) x‖ ≤ ε*(θ r)^p := by
  obtain ⟨roster,cover⟩ := WilsonOriginalCompactPoseCover.original coordinates K compact separated
  let core := univ.pi (fun _ : Fin (m+1) => Icc (1/3:ℝ) (2/3))
  have cc : IsCompact core := isCompact_univ_pi fun _ => isCompact_Icc
  let target (r : ℝ) (x : Points n) := ∑ k : Fin (p+1), (θ r:ℂ)^k.val*coeff k.val x
  have box (B : Box n (m+1)) : ∀ᶠ r in trail, ∀ x ∈ B.core, ∀ who : Viewers F,
      ‖iteratedFDeriv ℝ j (measured F who (pub r) v r) x - iteratedFDeriv ℝ j (target r) x‖ ≤ ε*(θ r)^p := by
    let wallet := 1+‖B.axes.symm.toContinuousLinearMap‖^j
    have rich : 0 < wallet := add_pos_of_pos_of_nonneg one_pos (pow_nonneg (norm_nonneg _) _)
    have clears (x : Fin (m+1) → ℝ) (unit : ∀ i, x i ∈ Icc (0:ℝ) 1) : B.origin+B.axes x ∈ conf n := by
      intro a b eq
      by_contra h
      have h' := B.separated x unit a b h
      change (B.origin+B.axes x) a = (B.origin+B.axes x) b at eq
      rw [eq,dist_self] at h'
      exact B.positive.not_ge h'
    have sc (k) (x) (unit : ∀ i, x i ∈ Icc (0:ℝ) 1) :
        ContDiffAt ℝ ∞ (fun z => coeff k (B.origin+B.axes z)) x :=
      ((smooth k).contDiffAt ((conf_open n).mem_nhds (clears x unit))).comp x
        (contDiffAt_const.add B.axes.contDiff.contDiffAt)
    have inner (x) (hx : x ∈ core) (i) : x i ∈ Ioo (1/6:ℝ) (5/6) := by
      have h := hx i (mem_univ i)
      exact ⟨lt_of_lt_of_le (by norm_num) h.1,lt_of_le_of_lt h.2 (by norm_num)⟩
    have bill := WilsonOriginalHomogeneousViewerShape.original run Z d v B.positive clock B.origin
      B.axes.toContinuousLinearMap B.columns (fun _ => 1/6) (fun _ => 5/6) (fun _ => by norm_num)
      (fun _ => by norm_num) B.separated (fun k x => coeff k (B.origin+B.axes x)) (Dtest B) (earned B) sc core cc inner p j (div_pos eps rich)
    have radial : ∀ᶠ r in trail, 0 < r := self_mem_nhdsWithin
    filter_upwards [bill,radial,clock.positive] with r income hr hw x hx who
    have zc : B.atPhysical x ∈ core := fun i _ => ⟨(hx i).1.le,(hx i).2.le⟩
    have unit (i) : B.atPhysical x i ∈ Icc (0:ℝ) 1 :=
      ⟨(by norm_num : (0:ℝ) ≤ 1/3).trans (hx i).1.le,(hx i).2.le.trans (by norm_num)⟩
    have hconf := clears _ unit
    have measure : ContDiffOn ℝ j (measured F who (pub r) v r) (conf n) := by
      intro y hy
      have inc := (S.class_smooth _ (spectate F who).smooth (fun i=>⟨d i,pub r (d i) (v i)⟩)).contDiffAt
        ((conf_open n).mem_nhds (Work.A05.smul_conf hr hy))
      exact ((inc.comp y (contDiffAt_id.const_smul r)).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffWithinAt
    have paper : ContDiffOn ℝ j (target r) (conf n) := ContDiffOn.sum fun k _ =>
      contDiffOn_const.mul ((smooth k.val).of_le (WithTop.coe_le_coe.mpr le_top))
    have paid := income (B.atPhysical x) zc who
    change ‖iteratedFDeriv ℝ j (fun z => measured F who (pub r) v r (B.origin+B.axes.toContinuousLinearMap z)) (B.atPhysical x) -
      iteratedFDeriv ℝ j (fun z => target r (B.origin+B.axes.toContinuousLinearMap z)) (B.atPhysical x)‖ ≤ _ at paid
    have here : B.origin+B.axes.toContinuousLinearMap (B.atPhysical x)=x := B.places x
    rw [WilsonOriginalAffineShapeJets.original j _ (conf_open n) measure B.origin B.axes.toContinuousLinearMap (x:=B.atPhysical x) hconf,
      WilsonOriginalAffineShapeJets.original j _ (conf_open n) paper B.origin B.axes.toContinuousLinearMap (x:=B.atPhysical x) hconf,here] at paid
    apply (WilsonOriginalUnchartedTensor.original B.axes _ _).trans
    calc
      _ ≤ (ε/wallet*(θ r)^p)*wallet := mul_le_mul paid (by simp [wallet]) (by positivity) (by positivity)
      _ = ε*(θ r)^p := by field_simp
  filter_upwards [roster.eventually_all.mpr fun B _ => box B] with r bounds x hx who
  obtain ⟨B,hB,hx⟩ := cover x hx
  exact bounds B hB x hx who

end YM.Integration.WilsonOriginalGlobalViewerShape
