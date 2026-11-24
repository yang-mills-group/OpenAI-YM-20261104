import YM.Integration.WilsonOriginalHomogeneousShapeWithdrawal
import YM.Integration.WilsonOriginalCartesianJetComponents
import YM.Integration.WilsonOriginalFiniteSpatialTensor
import YM.Integration.WilsonOriginalInteriorShapeValues
import YM.Integration.WilsonOriginalHomogeneousCompactInvoice
/-! The signed compact test on the elected homogeneous physical mean supplies
both inputs of the Fourier readback on its real box. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalHomogeneousShapeTensor
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

include run in
theorem original {n m : ℕ} (d : Fin n → ℕ) (v : (i : Fin n) → RG17.Free R.family (d i))
    {η : ℝ} (gap : 0 < η) {u : ℝ → ℝ} (clock : Coupling G u)
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
          (u r:ℂ)^k.val*(∫ x, (∏ i,φ i (x i))*coeff k.val x)‖ ≤ C*u r^q*A)
    (sc : ∀ k x, (∀ i, x i ∈ Icc (0:ℝ) 1) → ContDiffAt ℝ ∞ (coeff k) x)
    (K : Set (Fin (m+1) → ℝ)) (compact : IsCompact K) (inside : ∀ x ∈ K, ∀ i, x i ∈ Ioo (l i) (h i))
    (p j : ℕ) {ε : ℝ} (eps : 0 < ε) :
    ∀ᶠ r in trail, ∀ x ∈ K, ‖iteratedFDeriv ℝ j
      (fun y => S.classMoment S d (r • (origin+embed y)) (fun t => homogeneous F J Z r (d t) (v t))-
        ∑ k : Fin (p+1), (u r:ℂ)^k.val*coeff k.val y) x‖ ≤ ε*u r^p := by
  let B := ((m+1:ℕ):ℝ)^j
  have positive : 0 < B := pow_pos (Nat.cast_pos.mpr (Nat.succ_pos m)) _
  let underlying := fun (r : ℝ) (y : Fin (m+1) → ℝ) =>
    S.classMoment S d (r • (origin+embed y)) (fun t => homogeneous F J Z r (d t) (v t))-
        ∑ k : Fin (p+1), (u r:ℂ)^k.val*coeff k.val y
  have every (axis : Fin j → Fin (m+1)) : ∀ᶠ r in trail, ∀ x ∈ K,
      ‖WilsonOriginalSpatialProductRule.word (List.ofFn axis).reverse (underlying r) x‖ ≤ (ε/B)*u r^p :=
    WilsonOriginalHomogeneousShapeWithdrawal.original run Z d v gap clock origin embed direction l h
      left right room coeff Dtest earned sc K compact inside p (List.ofFn axis).reverse (div_pos eps positive)
  let O := univ.pi (fun i : Fin (m+1) => Ioo (l i) (h i))
  have opn : IsOpen O := isOpen_set_pi finite_univ (fun _ _ => isOpen_Ioo)
  have radial : ∀ᶠ r in trail, 0 < r := self_mem_nhdsWithin
  filter_upwards [eventually_all.mpr every,radial,clock.positive] with r salaries hr warm x hx
  have smooth : WilsonOriginalSpatialProductRule.Regular O (underlying r) := by
    intro y hy
    have cube (i : Fin (m+1)) : y i ∈ Icc (0:ℝ) 1 :=
      ⟨(left i).le.trans (hy i (mem_univ i)).1.le,(hy i (mem_univ i)).2.le.trans (right i).le⟩
    have clear : origin+embed y ∈ conf n := by
      intro a b eq
      by_contra different
      have g := room y cube a b different
      change (origin+embed y) a = (origin+embed y) b at eq
      rw [eq,dist_self] at g
      exact gap.not_ge g
    have gain := (S.class_smooth S F.room.kernel.smooth
      (fun t => ⟨d t,homogeneous F J Z r (d t) (v t)⟩)).contDiffAt
      ((conf_open n).mem_nhds (Work.A05.smul_conf hr clear))
    have lin : ContDiffAt ℝ ∞ (fun z => r • (origin+embed z)) y :=
      (contDiffAt_const.add embed.contDiff.contDiffAt).const_smul r
    apply (gain.comp y lin).sub
    exact ContDiffAt.sum (fun k _ => contDiffAt_const.mul (sc k.val y cube))
  have paid (axis : Fin j → Fin (m+1)) :
      ‖iteratedFDeriv ℝ j (underlying r) x (fun k => Pi.single (axis k) (1:ℝ))‖ ≤ (ε/B)*u r^p := by
    have h := WilsonOriginalCartesianJetComponents.original j axis (underlying r) opn smooth
      (show x ∈ O from fun i _ => inside x hx i)
    dsimp only at h
    rw [h]
    exact salaries axis x hx
  calc
    ‖iteratedFDeriv ℝ j (underlying r) x‖ ≤ B*((ε/B)*u r^p) :=
      WilsonOriginalFiniteSpatialTensor.original _ (mul_nonneg (div_pos eps positive).le (pow_nonneg warm.le _)) paid
    _ = ε*u r^p := by field_simp

end YM.Integration.WilsonOriginalHomogeneousShapeTensor
