import YM.OPE.Vitrines.Budget
import YM.FullVolume.Mark.Latch
import YM.MergeProof.Montage
/-!
# Regular reserve in the FullVolume/RG17 coupled column representation

Keep the +2 reserve in `reservedMass` *at the same time* as the forced budget,
through the FullVolume Keeper's actual reseating and Tools, not just on
some choice of transfer data after an existence proof. This file gives the accounting
lemma for that on `book`, countable merges etc. Parts adapted from
Mark/Carts (the slightly weaker weighted estimate), Vitrines/Jewel
(separate purchases), Extra/SOURCE_HISTORIES/Pencil, Mark/Slate.

The anchored reserve uses the SAME supported derivative seminorm and price B;
locations, inflated regular supports, threshold & order are not changed after pricing.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Pier
open Finset Function Set Filter MeasureTheory Lattice Wilson RG Source Labels
  Extra.Histories Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat
  MergeProof MergeProof.Matric
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

/-- `q` allows anticipating a turn cost on the regular sector. No such factor on
    the forced sector. `Tab` includes positivity of divisor κ and the original parts
    of remBound; the below strengthening keeps both AND the +2 exponential-weight
    reserve within the same total charge. No relation to large-field probability
    is assumed or claimed. -/
def Room {G : Gauge} {d : ℕ} {F : Labels.Frame G d} {n : Side}
    (P : Coefficient F n) (o : Site n) (R : Rep G n) (κ q c : ℝ) : Prop :=
  ∃ a b : ℝ, Tab P o R κ a b ∧ Blown P o R a ∧ q * a + b ≤ c

abbrev rotationBudget (B : BudgetPoint) : ℝ := turnCost B.order B.power

lemma rotationBudget_one (B : BudgetPoint) : 1 ≤ rotationBudget B :=
  one_le_pow₀ (one_le_mul_of_one_le_of_one_le one_le_two (one_le_pow₀ one_le_two))

variable {G : Gauge} {d : ℕ} {F : Labels.Frame G d} {n : Side}
    {o : Site n} {R : Rep G n} {Y : Hol G}
    {P : Coefficient F n} {κ a b q c c' : ℝ}

namespace Room

lemma unturn (h : Room P o R κ q c) (hq : 1 ≤ q) : Room P o R κ 1 c := by
  obtain ⟨u,v,h,hB,hp⟩ := h
  exact ⟨u,v,h,hB,(add_le_add (mul_le_mul_of_nonneg_right hq h.first) le_rfl).trans hp⟩

lemma larger (h : Room P o R κ q c) (hc : c ≤ c') : Room P o R κ q c' := by
  obtain ⟨a,b,h,hB,hp⟩ := h
  exact ⟨a,b,h,hB,hp.trans hc⟩

lemma conventional (h : Room P o R κ 1 c) : P.remBound o R κ c := by
  obtain ⟨a,b,h,hB,hp⟩ := h
  exact h.bound (by simpa using hp)

lemma regular (h : Room P o R κ 1 c) : Blown P o R c := by
  obtain ⟨a,b,h,hB,hp⟩ := h
  rw [one_mul] at hp
  exact hB.enlarge ((le_add_of_nonneg_right h.second).trans hp)

/-- The actual countable (support, slot) book retains all this reserve when closed
about the given Keeper. In particular this is the strengthened-price counterpart to
Carts/wages on the exact same `capture`; it invokes *its* forced reseating estimate
(no picking cheaper addresses). -/
theorem close (h : Room P 0 R κ q c) (hf : P.Format 0 Y R)
    (K : Keeper R.p R.activities) : Room (tell (closeK K P)) 0 R κ q c := by
  obtain ⟨a,b,h,⟨e,he,he'⟩,hb⟩ := h
  refine ⟨a,b,wages P K hf h, ?_, hb⟩
  change Blown (book P.x (capture P K)) 0 R a
  let f := tongue P.support
  let t := extend f e 0
  have hz i : t (f i) = e i := f.injective.extend_apply ..
  have hM i : mapSeat (f i) = P.support i := leased P hf i
  refine ⟨t,Local.sumBudget_pass f _ ?_ ?_,fun i => ?_⟩
  · change SumBudget (fun i => reservedMass R.p (mapSeat (n:=n) (f i)) (t (f i))) a
    simp_rw [hM,hz]
    exact he
  · intro i hi
    rw [show t i = 0 from extend_apply' _ _ _ hi,reservedMass,mul_zero]
  change R.p.supBounds 0 (mapSeat i) (liveE P i) (t i)
  by_cases hi : i ∈ Set.range f
  · obtain ⟨i,rfl⟩ := hi
    rw [hM,hz,show liveE P (f i)=P.regular i from f.injective.extend_apply ..]
    exact he' i
  rw [liveE,extend_apply' _ _ _ hi,show t i=0 from extend_apply' _ _ _ hi]
  exact (regular0 ..).2

lemma combine {ι : Type*} (e : ℕ ≃ ι × ℕ) {P : ι → Coefficient F n}
    {s : ι → ℝ} (hq : 1 ≤ q) (hκ : 0 < κ)
    (h : ∀ j, Room (P j) o R κ q (s j)) (hs : Summable s) :
    Room (Extra.Histories.merge e P) o R κ q (∑' i, s i) := by
  choose r u hr hh hu using h
  have hp : Summable r := hs.of_nonneg_of_le (fun i => (hh i).price)
    (fun i => (le_mul_of_one_le_left (hh i|>.price) hq).trans
      ((le_add_of_nonneg_right (hr i).second).trans (hu i)))
  have hv : Summable u := hs.of_nonneg_of_le (fun i => (hr i).second)
    (fun i => (le_add_of_nonneg_left
      (mul_nonneg (zero_le_one.trans hq) (hr i).first)).trans (hu i))
  refine ⟨_,_,(merge_tab e P hκ hr hp hv).1,Blown.joins e hh hp,?_⟩
  rw [← tsum_mul_left,← (hp.mul_left q).tsum_add hv]
  exact ((hp.mul_left q).add hv).tsum_le_tsum hu hs

lemma stretchTab (h : Tab P o R κ a b) (x : ℂ) :
    Tab (stretch x P) o R κ (‖x‖*a) (‖x‖*b) := by
  obtain ⟨h,ha,hb,⟨e,he,he'⟩,u,hu,hv⟩ := h
  refine ⟨h,mul_nonneg (norm_nonneg _) ha,mul_nonneg (norm_nonneg _) hb,
    ⟨fun i => ‖x‖ * e i,?_,fun i => Next.Foundations.bound_smul _ (he' i)⟩,
    fun i => ‖x‖*u i, ?_, fun i => ⟨mul_nonneg (norm_nonneg _) (hv i).1,fun U => ?_⟩⟩
  · simp_rw [mass_scale]; exact budget_scale he (norm_nonneg _)
  · simp_rw [mass_scale,mul_left_comm κ ‖x‖ b]; exact budget_scale hu (norm_nonneg _)
  rw [show (stretch x P).forced i U=x • P.forced i U from rfl,norm_smul]
  exact mul_le_mul_of_nonneg_left ((hv i).2 U) (norm_nonneg _)

lemma weighted (h : Room P o R κ q c) (x : ℂ) : Room (stretch x P) o R κ q (‖x‖ * c) := by
  obtain ⟨a,b,ha,h,hb⟩ := h
  refine ⟨_,_, stretchTab ha x, h.stretchable x,?_⟩
  rw [mul_left_comm q ‖x‖,← mul_add]
  exact mul_le_mul_of_nonneg_left hb (norm_nonneg _)

lemma auditioned {B : SectionData F} (z : Extra.Histories.Motion)
    (S : R.activities.Moves z.1 0) (hn : 2 ≤ n.val) (ht : B.Sound Y)
    (hf : P.Format 0 Y R) (h : Room P 0 R κ (rotationBudget R.p) c) :
    Room (audition S P) 0 R κ 1 c := by
  obtain ⟨a,b,ha,h₀,hb⟩ := h
  obtain ⟨-, -, he, -⟩ := audition_receipt z S hn ht hf ha
  refine ⟨_,_,he,?_,?_⟩
  · simpa [affine] using h₀.spin S hf hn
  simpa using hb

lemma blank (hκ : 0 < κ) (hc : 0 ≤ c) : Room (book (F:=F) (0:F.Coeff) 0) 0 R κ q c := by
  refine ⟨0,0,⟨hκ,le_rfl,le_rfl,⟨0,budget0 ..,fun i=>(regular0 ..).2⟩,
    fun i=>0,by rw [mul_zero]; exact budget0 ..,fun i=> ⟨le_rfl,fun U=> (norm_zero (E:=ℂ)).le⟩⟩,
    ?_,by simpa using hc⟩
  refine ⟨fun _ => 0,?_,fun i => (regular0 ..).2⟩
  simp_rw [reservedMass,mul_zero]
  exact sumBudget_zero le_rfl

lemma base (x : F.Coeff) (hc : 0 ≤ c) (hκ : 0 < κ) :
    Room (Extra.Histories.primary o x) o R κ q c := by
  obtain ⟨a,b,h,h'⟩ := rem_tabs.mp (primary_rem (o:=o) (R:=R) x hκ)
  have hs : a = 0 := by linarith [h.first,h.second]
  subst a
  have he : b = 0 := by linarith [h.second]
  subst b
  exact ⟨0,0,h,Blown.primary _ le_rfl,by simpa using hc⟩

end Room
end YM.Pier
