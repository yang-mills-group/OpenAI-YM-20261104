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
namespace YM.Integration.WilsonOriginalHomogeneousViewerShape
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

include run in
theorem original {n m : ℕ} (d : Fin n → ℕ) (v : (i : Fin n) → RG17.Free R.family (d i))
    {η : ℝ} (gap : 0 < η) (clock : Coupling G θ)
    (origin : Points n) (embed : (Fin (m+1) → ℝ) →L[ℝ] Points n)
    (direction : ∀ i, ‖embed (Pi.single i (1:ℝ))‖ ≤ 1) (l h : Fin (m+1) → ℝ)
    (left : ∀ i, 0 < l i) (right : ∀ i, h i < 1)
    (room : ∀ x : Fin (m+1) → ℝ, (∀ i, x i ∈ Icc (0:ℝ) 1) → ∀ j k : Fin n,
       j ≠ k → η ≤ dist ((origin+embed x) j) ((origin+embed x) k))
    (coeff : ℕ → (Fin (m+1) → ℝ) → ℂ) (Dtest : ℕ)
    (earned : ∀ q : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ r in trail,
      ∀ φ : Fin (m+1) → ℝ → ℂ, (∀ i, ContDiff ℝ ∞ (φ i)) →
        (∀ i t, t ∉ Icc (l i) (h i) → φ i t = 0) → ∀ A : ℝ, 0 ≤ A →
        (∀ o : Fin (m+1) → ℕ, (∀ i, o i ≤ Dtest) → ∀ x : Fin (m+1) → ℝ,
          ‖∏ i, iteratedDeriv (o i) (φ i) (x i)‖ ≤ A) →
        ‖(∫ x, (∏ i,φ i (x i))*(fun (r : ℝ) (x : Fin (m+1) → ℝ) => S.classMoment S d (r • (origin+embed x)) (fun j => homogeneous F J Z r (d j) (v j))) r x) - ∑ k : Fin (q+1),
          (θ r:ℂ)^k.val*(∫ x, (∏ i,φ i (x i))*coeff k.val x)‖ ≤ C*θ r^q*A)
    (sc : ∀ k x, (∀ i, x i ∈ Icc (0:ℝ) 1) → ContDiffAt ℝ ∞ (coeff k) x)
    (K : Set (Fin (m+1) → ℝ)) (compact : IsCompact K) (inside : ∀ x ∈ K, ∀ i, x i ∈ Ioo (l i) (h i))
    (p j : ℕ) {ε : ℝ} (eps : 0 < ε) :
    ∀ᶠ r in trail, ∀ x ∈ K, ∀ who : Viewers F,
      ‖iteratedFDeriv ℝ j (fun z => measured F who (pub r) v r (origin+embed z)) x -
        iteratedFDeriv ℝ j (fun z => ∑ k : Fin (p+1), (θ r:ℂ)^k.val*coeff k.val z) x‖ ≤ ε*(θ r)^p := by
  have cube {x} (hx : x ∈ K) (i : Fin (m+1)) : x i ∈ Icc (0:ℝ) 1 :=
    ⟨(left i).le.trans (inside x hx i).1.le,(inside x hx i).2.le.trans (right i).le⟩
  have clear (x) (hx : x ∈ K) : origin+embed x ∈ conf n := by
    intro a b eq
    by_contra different
    have g := room x (cube hx) a b different
    change (origin+embed x) a = (origin+embed x) b at eq
    rw [eq,dist_self] at g
    exact gap.not_ge g
  have half : 0 < ε/2 := half_pos eps
  have mean := WilsonOriginalHomogeneousShapeTensor.original run Z d v gap clock origin embed direction l h
    left right room coeff Dtest earned sc K compact inside p j half
  have views := WilsonOriginalAffineViewerJets.original run Z v clock origin embed K compact clear j p half
  have radial : ∀ᶠ r in trail, 0 < r := self_mem_nhdsWithin
  filter_upwards [mean,views,radial] with r income phases hr x hx who
  let A := fun z => measured F none (pub r) v r (origin+embed z)
  let goal := fun z => ∑ k : Fin (p+1), (θ r:ℂ)^k.val*coeff k.val z
  have sm : ContDiffAt ℝ j A x := by
    have inc := (S.class_smooth S F.room.kernel.smooth (fun i => ⟨d i,pub r (d i) (v i)⟩)).contDiffAt
      ((conf_open n).mem_nhds (Work.A05.smul_conf hr (clear x hx)))
    have lin : ContDiffAt ℝ ∞ (fun z => r • (origin+embed z)) x :=
      (contDiffAt_const.add embed.contDiff.contDiffAt).const_smul r
    exact (inc.comp x lin).of_le (WithTop.coe_le_coe.mpr le_top)
  have sg : ContDiffAt ℝ j goal x :=
    (ContDiffAt.sum (fun (k : Fin (p+1)) _ => contDiffAt_const.mul (sc k.val x (cube hx)))).of_le
      (WithTop.coe_le_coe.mpr le_top)
  have base : ‖iteratedFDeriv ℝ j (A-goal) x‖ ≤ ε/2*(θ r)^p := income x hx
  rw [iteratedFDeriv_sub_apply sm sg] at base
  apply (norm_sub_le_norm_sub_add_norm_sub _ (iteratedFDeriv ℝ j A x) _).trans
  exact (add_le_add (phases x hx who none) base).trans (by ring_nf; rfl)

end YM.Integration.WilsonOriginalHomogeneousViewerShape
