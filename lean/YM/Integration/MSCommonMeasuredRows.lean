import YM.Integration.MSPhysicalDeckRemoval
import YM.Integration.MSNormalizedFeeReadout
import YM.Integration.MSExactGridReadout

/-! Both independently prescribed ordinary MS populations on one
original finite Wilson regulator at precisely the same q-adic positions. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.MSCommonMeasuredRows

open Filter Function FVA2 Lattice MS MS.Local.Physical MS.Menus MS.Land MS.Rake MS.Tone
open MS.Dial MS.Tide MS.Tide.PeakT MS.Orbit MS.Fleet
open MSNormalizedFeeReadout
open scoped Topology Classical

variable {G : Gauge} {A B : Deck G} {QA : Booked A} {QB : Booked B}
variable (V : Warehouse G) (D : MS_Data G QA) (S : MS_Data G QB) (P : Prescription A)
variable {I W : Type} [Fintype W] [LinearOrder W]

def marked (E : MSPhysicalDeckChange.Fees B A) (u : W → Label B) (T : Trial I W) (μ : ℝ)
    (i : I) : PowerSeries ℂ :=
  price V P (dimT T.side i) (Label.h ∘ u) (T.head i) (fun w => T.off w i) μ
    (T.profile.θ i) (fun w => E (u w).h (u w).item)

def native (u : W → Label A) (T : Trial I W) (μ : ℝ) (i : I) : PowerSeries ℂ :=
  price V P (dimT T.side i) (Label.h ∘ u) (T.head i) (fun w => T.off w i) μ
    (T.profile.θ i) (Matched.tFees P u)

theorem declared (E : MSPhysicalDeckChange.Fees B A) (u : W → Label B)
    (T : Trial I W) (μ : ℝ) (i : I) (k : ℕ) :
    PowerSeries.coeff k (marked V P E u T μ i) =
      fare (Label.h ∘ u) T.profile (MSPhysicalDeckRemoval.finite V P E u T μ) Finset.univ k i := by
  rw [marked, price, PowerSeries.coeff_C_mul, PowerSeries.coeff_map]
  rfl

theorem selected (u : W → Label A) (T : Trial I W) (μ : ℝ) (i : I) (k : ℕ) :
    PowerSeries.coeff k (native V P u T μ i) =
      fare (Label.h ∘ u) T.profile (MixedStory.ordinary V T P μ u) Finset.univ k i := by
  rw [native, price, PowerSeries.coeff_C_mul, PowerSeries.coeff_map]
  rfl

def Reads {C : Deck G} {QC : Booked C} (M : MS_Data G QC) (u : W → Label C)
    (T : Trial I W) (μ : ℝ) (l : Filter I) (x : W → QP) (F : I → PowerSeries ℂ) :=
  ∀ k, PeakT l T.profile mildG
    (fun i => PowerSeries.coeff k (F i) - Dial.tour M u μ x Finset.univ k)

def Grids (E : MSPhysicalDeckChange.Fees B A) : Prop :=
  ∀ (W : Type) [Fintype W] [LinearOrder W] (q : Side) (_ : 1 < q.val)
        (μ : ℝ) (m : ℕ) (z : W → Cover)
        (_ : Injective fun w => MSExactGridReadout.point q m (z w)),
      ∃ k : ℕ, ∀ o : ℕ → Cover, (∀ j, Tiles.Daily q j (o j)) →
        let x := fun w => MSExactGridReadout.point q m (z w)
        let T := Tiles.ladder x q μ o k
        Uses T atTop μ ∧
        (∀ u : W → Label A, Reads D u T μ atTop x (native V P u T μ)) ∧
        ∀ u : W → Label B, Reads S u T μ atTop x (marked V P E u T μ)

theorem actual (E : MSPhysicalDeckChange.Fees B A) (hG : G.Simple)
    (hP : MixedStory.AllProfiles D V P) (hE : MSPhysicalDeckChange.Implements (V.native A) P.team S E) :
    Grids V D S P E := by
  intro W _ _ q hq μ m z hz
  obtain ⟨k, hk⟩ := MSExactGridReadout.trial q hq μ m z hz
  refine ⟨k, ?_⟩
  intro o ho
  let x := fun w => MSExactGridReadout.point q m (z w)
  let T := Tiles.ladder x q μ o k
  obtain ⟨hr, hp⟩ := hk o ho
  refine ⟨hr, ?_, ?_⟩
  · intro u d
    have h := (MixedStory.accuracy D V T P μ u atTop hP hr Finset.univ d).2.2
    apply PeakT.fromζ h
    filter_upwards [hp] with i hi
    rw [selected]
    dsimp only [Pi.sub_apply]
    rw [hi]
  · intro u d
    have h := (MSPhysicalDeckRemoval.actual V P E S u T μ atTop hG hr (by
      rw [MSPhysicalDeckChange.bulk S D]
      exact hP.1.bulk) hE Finset.univ d).2
    apply PeakT.fromζ h
    filter_upwards [hp] with i hi
    rw [declared]
    dsimp only [Pi.sub_apply]
    rw [hi]

theorem both (hG : G.Simple) (hP : MixedStory.AllProfiles D V P) :
    ∃ E : MSPhysicalDeckChange.Fees B A,
      MSPhysicalDeckChange.Implements (V.native A) P.team S E ∧ Grids V D S P E := by
  obtain ⟨E, _, hE⟩ := MSPhysicalDeckChange.selected (V.native A) S D P hG hP.1
  exact ⟨E, hE, actual V D S P E hG hP hE⟩

end YM.Integration.MSCommonMeasuredRows
