import YM.Integration.FVA1Physical.Marked.ColorBudget
import YM.Integration.FVA1Physical.Marked.ColorLog

/-! Summability of the actual underlying countable log rows follows from
the complete represented norm, before any recombination of source slots. -/
set_option autoImplicit false
set_option maxHeartbeats 950000
noncomputable section
namespace YM.Integration.FVA1Physical.Marked
open MeasureTheory Lattice RG Wilson Marker LocalComparison RG3.Script.Picnic Push.AbsoluteSums
open Overlay RG3.Forms
open scoped Classical BigOperators
variable {G : Gauge} {I : Type} [DecidableEq I] [Fintype I] {B : Census I}
    {n : Side} {P : Rep G n} {o : I→Site n}

private theorem collect {J : Type} (tag : J→Finset I) (proper : ∀ j,(tag j).Nonempty) (f : J→ℝ)
    (hn : ∀ j,0 ≤ f j) (fund : ∀ k,Summable (fun j=>if k∈tag j then f j else 0)) : Summable f := by
  let ans (k : I) (j : J) := if k∈tag j then f j else 0
  have has := summable_sum (s:=Finset.univ) (f:=ans) fun k _=>fund k
  apply has.of_nonneg_of_le hn
  intro i
  obtain ⟨k,hk⟩ := proper i
  calc
    _ = ans k i := (if_pos hk).symm
    _ ≤ ∑ j,ans j i := Finset.single_le_sum (f:=fun j=>ans j i) (fun j _=>by change 0 ≤ if j∈tag i then f i else 0; split <;> first | exact hn i | exact le_rfl) (Finset.mem_univ k)

theorem grain_value {S : Support n} {p : BudgetPoint} {f : Config G n→ℂ} {a : Site n} {c : ℝ}
    (h : Mix.grain p S f a c) {v : Config G n} (healthy : Healthy p.threshold S v) : ‖f v‖ ≤ c := by
  obtain ⟨d,pos,all,each⟩ := h
  have v0 := each [] (by simp) (by simp) v healthy
  apply v0.trans
  apply le_trans _ all
  have use := Finset.single_le_sum (fun j (_ : j ∈ Finset.range (p.order+1))=>
    div_nonneg (pos j) (Nat.cast_nonneg j.factorial)) (Finset.mem_range.mpr (Nat.zero_lt_succ p.order))
  change d 0 ≤ _
  simpa only [Nat.factorial_zero,Nat.cast_one,div_one] using use

/-- The countable native series whose coefficients are polarized are
honest summable series for every incoming test and every configuration. -/
theorem log_banks_summable {X : Type*} {T : Taste X o P B} {w : I→ℝ} {κ a b : ℝ}
    (H : FullBudget P.p T w κ a b) (t : X) (v : Config G n) :
    Summable (fun i=> (T.leaf t).contents.ray i v) ∧
    Summable (fun i=> Poly.send (T.tag i) (T.score t i)) := by
  let W := fun i=>Poly.toll w (T.menu.rays i)*P.p.mass (T.menu.branch i) (H.white i)
  let C := fun i=>Poly.toll w (T.tag i)*P.p.mass (T.site i) (H.gold i)
  let act := H.active t
  have wn i : 0 ≤ W i := mul_nonneg (Poly.worth H.radii _).le (mul_nonneg (Real.exp_nonneg _) (H.white_nonnegative i))
  have cn i : 0 ≤ C i := mul_nonneg (Poly.worth H.radii _).le (mul_nonneg (Real.exp_nonneg _) (H.gold_nonnegative i))
  have white : Summable W := collect _ act.articles.proper W wn fun j=>
    (H.regularTotal j).choose_spec.choose_spec.1.2.1
  have gold : Summable C := collect _ act.captions.card C cn fun j=>
    (H.regularTotal j).choose_spec.choose_spec.2.1.2.1
  constructor
  · apply (Poly.budgeted H.radii white ?_).1
    intro i
    rw [Bands.ray,Poly.solo]
    apply mul_le_mul_of_nonneg_left _ (Poly.worth H.radii _).le
    apply le_trans _ (P.p.loMass _ _ (H.white_nonnegative i))
    change ‖masked P.p.threshold (T.menu.branch i) (T.menu.regular t i) v‖ ≤ H.white i
    obtain ⟨j,hj⟩ := act.articles.proper i
    by_cases hy : Healthy P.p.threshold (T.menu.branch i) v
    · rw [masked_eq _ _ _ _ hy]
      exact grain_value ((H.regular i).controls t j hj) hy
    rw [masked_ne _ _ _ _ hy,norm_zero]
    exact H.white_nonnegative i
  apply (Poly.budgeted H.radii gold ?_).1
  intro i
  rw [Poly.solo]
  exact mul_le_mul_of_nonneg_left ((H.caption t i).trans (P.p.loMass _ _ (H.gold_nonnegative i))) (Poly.worth H.radii _).le

end YM.Integration.FVA1Physical.Marked
