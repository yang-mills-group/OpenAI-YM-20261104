import YM.GradedFar.Continuation.Bills

/-!
# Carry discarded product terms also for the true versus predictor comparison
-/
namespace YM.FVA2.GradedFar.Continuation
noncomputable section
open Filter Set Real Topology Function PowerSeries
open O.Enh
open scoped Topology BigOperators Classical

section
variable {I J : Type} {b : Board I} {v w : ℝ} {t : I → ℝ}
variable {F Q : I → PowerSeries ℂ} {p k : ℕ}
def Ledger (b : Board I) (p : ℕ) (v : ℝ) (F : I → PowerSeries ℂ) : Prop :=
  ∀ j ≤ p, Bill b 0 v (fun i => coeff j (F i))
namespace Ledger
lemma from_charge {F : J → ℝ → PowerSeries ℂ} (h : ChargeP (p+1) v F) (r : I → J) :
    Ledger b p v (fun i => F (r i) (b.s i)) := fun j hj => Bill.of_rain (h j (by omega)) r
lemma prod (h : Ledger b p v F) (he : Ledger b p w Q) : Ledger b p (v+w) (fun i => F i*Q i) := by
  intro j hj; simp_rw [coeff_mul]; refine Bill.sum _ fun k hk => ?_
  have hu := Finset.HasAntidiagonal.mem_antidiagonal.mp hk
  exact (h k.1 (by omega)).times (he k.2 (by omega))
lemma const (x : PowerSeries ℂ) : Ledger b p 0 (fun _ => x) :=
  fun j _ => Bill.of_bounded _ ‖coeff j x‖ (by filter_upwards with i; exact le_rfl)
lemma product (s : Finset J) (a : J → ℝ) {F : J → I → PowerSeries ℂ} (h : ∀ i ∈ s, Ledger b p (a i) (F i)) :
    Ledger b p (∑ j ∈ s, a j) (fun i => ∏ j ∈ s, F j i) := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, Finset.sum_empty]; exact const _
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi, Finset.prod_insert hi]
    exact prod (h i (Finset.mem_insert_self ..)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))
lemma monotone (h : Ledger b p w F) (hq : k ≤ p) : Ledger b k w F :=
  fun j hj => h j (hj.trans hq)

variable (ht : ∀ᶠ i in b.l, |t i| ≤ 2 * b.g i)
include ht
lemma exponent (k : ℕ) : Bill b k 0 (fun i => (t i:ℂ)^k) := by
  refine ⟨2^k, by positivity,0,?_⟩
  filter_upwards [ht] with i hi
  rw [norm_pow,Complex.norm_real,Real.norm_eq_abs,post,neg_zero,zero_mul,exp_zero,pow_zero,mul_one,mul_one]
  exact (pow_le_pow_left₀ (abs_nonneg _) hi k).trans_eq (mul_pow ..)
lemma evaluate (h : Ledger b p w F) : Bill b 0 w (fun i => crop p (t i) (F i)) := by
  simp only [crop_eq]; refine Bill.sum _ fun q hq => ?_
  simpa only [zero_add] using ((exponent ht q).mono_fee le_rfl (Nat.zero_le _)).times (h q (Finset.mem_range_succ_iff.mp hq))
lemma recrop (h : Ledger b p v F) (he : Ledger b p w Q) :
    Bill b (p+1) (v+w) (fun i => crop p (t i) (F i)*crop p (t i) (Q i)-crop p (t i) (F i*Q i)) := by
  simp_rw [crop_mul,add_sub_cancel_left]
  unfold cross
  refine Bill.sum _ fun q hq => ?_
  obtain ⟨⟨hf,hg⟩,hm⟩ := (mem_pairsAbove p q).1 hq
  simpa only [zero_add] using ((exponent ht (q.1+q.2)).mono_fee le_rfl hm).earns
    ((h q.1 hf).times (he q.2 hg))
lemma below (h : Ledger b k w F) (hk : p ≤ k) :
    Bill b (p+1) w (fun i => crop k (t i) (F i) - crop p (t i) (F i)) := by
  induction k,hk using Nat.le_induction with
  | base => simp only [sub_self]; exact Bill.from_zero _
  | succ q hq ih =>
    have e i : crop (q+1) (t i) (F i) - crop p (t i) (F i) =
        (t i:ℂ)^(q+1) * coeff (q+1) (F i) + (crop q (t i) (F i)-crop p (t i) (F i)) := by
      simp only [crop_eq]; conv_lhs => lhs; rw [Finset.sum_range_succ]
      abel
    simp_rw [e]; refine Bill.plus ?_ (ih (h.monotone (Nat.le_succ q)))
    simpa only [zero_add] using ((exponent ht (q+1)).mono_fee le_rfl (show p+1 ≤ q+1 by omega)).earns
      (h (q+1) le_rfl)
end Ledger

/-- The actual-model field coordinates in budget of their separately evaluated
expansions. -/
def Priced (b : Board I) (p : ℕ) (t : I → ℝ) (v : ℝ) (A : I → ℂ) (F : I → PowerSeries ℂ) :=
  Ledger b p v F ∧ Bill b (p+1) v (fun i => A i-crop p (t i) (F i))
namespace Priced
variable (ht : ∀ᶠ i in b.l, |t i| ≤ 2 * b.g i)
variable {A B : I → ℂ}
include ht
lemma weight (h : Priced b p t v A F) : Bill b 0 v A := by
  have hz := h.1.evaluate ht
  have ha := h.2.mono_fee le_rfl (Nat.zero_le _)
  simpa only [sub_add_cancel] using ha.plus hz
lemma mul_exact (h : Priced b p t v A F) (he : Ledger b p w Q) :
    Bill b (p+1) (v+w) (fun i => A i * crop p (t i) (Q i)-crop p (t i) (F i*Q i)) := by
  have hp := h.2.earns (he.evaluate ht)
  have hr := hp.plus (h.1.recrop ht he)
  apply hr.apply_eq (Eventually.of_forall fun i => ?_)
  rw [sub_mul]; abel
lemma prod (h : Priced b p t v A F) (he : Priced b p t w B Q) :
    Priced b p t (v+w) (fun i => A i*B i) (fun i => F i*Q i) := by
  refine ⟨h.1.prod he.1,?_⟩
  have e := (h.weight ht).times he.2
  have q := h.mul_exact ht he.1
  refine (e.plus q).apply_eq (Eventually.of_forall fun i => ?_)
  rw [mul_sub]; abel
lemma product (s : Finset J) (v : J → ℝ) {A : J → I → ℂ} {F : J → I → PowerSeries ℂ}
    (h : ∀ i ∈ s, Priced b p t (v i) (A i) (F i)) :
    Priced b p t (∑ j ∈ s, v j) (fun i => ∏ j ∈ s, A j i) (fun i => ∏ j ∈ s, F j i) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty]
    refine ⟨Ledger.const _, (Bill.from_zero b).apply_eq (Eventually.of_forall fun x => ?_)⟩
    simp [crop]
  | insert j s hj ih =>
    simp only [Finset.prod_insert hj, Finset.sum_insert hj]
    exact prod ht (h j (Finset.mem_insert_self ..)) (ih fun k hk => h k (Finset.mem_insert_of_mem hk))
end Priced
end
end
end YM.FVA2.GradedFar.Continuation
