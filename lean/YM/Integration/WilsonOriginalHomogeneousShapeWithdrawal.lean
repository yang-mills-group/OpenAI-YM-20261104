import YM.Integration.WilsonOriginalInteriorShapeValues
import YM.Integration.WilsonOriginalHomogeneousCompactInvoice
/-! The signed compact test on the elected homogeneous physical mean supplies
both inputs of the Fourier readback on its real box. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalHomogeneousShapeWithdrawal
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
    (p : ℕ) (w : List (Fin (m+1))) {ε : ℝ} (eps : 0 < ε) :
    ∀ᶠ r in trail, ∀ x ∈ K, ‖WilsonOriginalSpatialProductRule.word w
      (fun y => S.classMoment S d (r • (origin+embed y)) (fun j => homogeneous F J Z r (d j) (v j))-
        ∑ k : Fin (p+1), (u r:ℂ)^k.val*coeff k.val y) x‖ ≤ ε*u r^p := by
  obtain ⟨price⟩ := WilsonOriginalHomogeneousCompactInvoice.original run Z d v gap clock
    origin embed direction l h left right room coeff Dtest earned
  have clear (x : Fin (m+1) → ℝ) (hx : ∀ j, x j ∈ Icc (0:ℝ) 1) : origin+embed x ∈ conf n := by
    intro j q same
    by_contra different
    have gap' := room x hx j q different
    change (origin+embed x) j = (origin+embed x) q at same
    rw [same,dist_self] at gap'
    exact gap.not_ge gap'
  apply WilsonOriginalInteriorShapeValues.original simple clock l h left right
    (fun r x => S.classMoment S d (r • (origin+embed x)) (fun j => homogeneous F J Z r (d j) (v j)))
    coeff _ sc price K compact inside p w eps
  have dates : ∀ᶠ r in trail, 0 < r := self_mem_nhdsWithin
  filter_upwards [dates] with r hr x hx
  have loc := (conf_open n).mem_nhds (Work.A05.smul_conf hr (clear x hx))
  have gain := (S.class_smooth S F.room.kernel.smooth
    (fun j => ⟨d j,homogeneous F J Z r (d j) (v j)⟩)).contDiffAt loc
  have map : ContDiffAt ℝ ∞ (fun y => r • (origin+embed y)) x :=
    (contDiffAt_const.add embed.contDiff.contDiffAt).const_smul r
  exact gain.comp x map

end YM.Integration.WilsonOriginalHomogeneousShapeWithdrawal
