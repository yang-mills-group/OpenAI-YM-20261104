import YM.Integration.WilsonOriginalPhysicalMeanModes
import YM.Integration.WilsonOriginalMeasuredGevreyBank

/-! The signed compact test on the elected homogeneous physical mean supplies
both inputs of the Fourier readback on its real box. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPurchasedMeanPrice
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
    (tested : ∀ q : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ r in trail, ∀ freq : Fin (m+1) → ℤ,
      ‖(∫ x, test l h freq x * S.classMoment S d (r • (origin+embed x))
        (fun j => homogeneous F J Z r (d j) (v j))) -
        ∑ k : Fin (q+1), (u r:ℂ)^k.val * (∫ x, test l h freq x * coeff k.val x)‖ ≤
        C*(u r)^q*(1+(height freq:ℝ))^Dtest) :
    Nonempty (Prices u (fun r freq => mFourierCoeff (localize 0 l h (fun x =>
      S.classMoment S d (r • (origin+embed x)) (fun j => homogeneous F J Z r (d j) (v j)))) freq)
      (fun k freq => mFourierCoeff (localize 0 l h (coeff k)) freq)) := by
  obtain ⟨B,D,bpos,dpos,physical⟩ := WilsonOriginalPhysicalMeanModes.original run Z d v gap clock embed direction
  refine ⟨⟨Dtest,2,D,Real.log 2/(2*B),by norm_num,dpos,by positivity,?_,?_⟩⟩
  · filter_upwards [physical,clock.positive,show ∀ᶠ r in trail, 0<r from self_mem_nhdsWithin] with r cash pos hr freq
    have exactCash := cash hr origin l h left right room freq
    have paid := WilsonOriginalGevreyFrequency.original (u r) ((size freq)^6) 1 B D pos (by positivity)
      (by norm_num) bpos _ (fun k => by
        have power : ((size freq)^6)^(2*k) = (height freq:ℝ)^k := by
          calc
            _ = (((size freq)^6)^2)^k := pow_mul _ 2 k
            _ = _ := by
              have square : ((size freq)^6)^2 = (height freq:ℝ) := by
                rw [← pow_mul]; exact size_pow freq
              exact congrArg (fun x : ℝ => x^k) square
        rw [power,one_mul]
        exact exactCash k)
    simpa only [mul_one] using paid
  · intro q
    obtain ⟨C,pos,fee⟩ := tested q
    refine ⟨C,pos,?_⟩
    filter_upwards [fee] with r wages freq
    have upper (i : Fin (m+1)) : h i ≤ (0 : Fin (m+1) → ℝ) i + 1 := by simpa using (right i).le
    simp only [WilsonOriginalFourierBoxIntegral.original 0 l h freq _ (fun i => (left i).le) upper,size_pow]
    exact wages freq

end YM.Integration.WilsonOriginalPurchasedMeanPrice
