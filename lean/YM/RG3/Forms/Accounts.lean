import YM.RG3.Forms.Feed
/-!
# Charge for finite slip factors from full original list

Cost area Hit with current geometric conventions, outside derivative weights
(using global sup on actual *discrepancies* made from original H etc on
exact masks---not a claimed global sup on unmasked E). Assume height at hit
for slips ≤ 1, so all intrinsic vac discrepancies (quiet coefficient
aggregated by support) have exp bound from mean value theorem / exp estimate
in Mathlib.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Forms.Feed
open Press Marker Lattice Wilson RG Function MeasureTheory Ac Extra.Trajectories Finset Push.Corrected Push.AbsoluteSums
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {α : Type*} {V : Type*} [DecidableEq V] {R : Census V} {n : Side} {G : Gauge}
variable (k : Feed G n R α)

def levy (u : α → ℝ) (c : Column R n) := ∑' i : k.office c,u (k.address i)

/-- Twice the coefficient for **both** marked and unmarked, simp. -/
def coin (u : α → ℝ) (c : Column R n) := Poly.send (domain c) (↑(2*k.levy u c):ℂ)

variable {w : V → ℝ} {u : α → ℝ} {δ a : ℝ} {B : ℕ}

lemma price_coin (hu : ∀ i,0 ≤ u i) (c : Column R n) : Poly.price w (k.coin u c)=Poly.toll w (domain c)*(2*k.levy u c) := by
  unfold coin; rw [Poly.solo,Complex.norm_real,Real.norm_of_nonneg]
  exact mul_nonneg zero_le_two (tsum_nonneg fun i => hu _)

lemma payment (hw : ∀ i,0 < w i) (_ha : 0 ≤ a) (h : k.Worth w B a u δ) :
    Hit region B (fun c => Poly.price w (k.coin u c)) a (2*δ) := by
  intro x; refine budget_finite (fun c => ?_) ?_
  · split
    · exact mul_nonneg (Poly.nonnegative hw _) (Real.exp_pos _).le
    exact le_rfl
  have hi : SumBudget (fun i => k.fee u w B a x i) δ := h.budget x
  have ht := hi.2.1.hasSum.tsum_fiberwise k.column
  change HasSum (fun c => ∑' i : k.office c,k.fee u w B a x (k.address i)) (∑' i,k.fee u w B a x i) at ht
  let E z := Real.exp (a*coverNumber B (region (R:=R) (n:=n) z))
  let f c := if x ∈ region c then Poly.price w (k.coin u c)*E c else 0
  calc
    ∑ c, f c = 2*∑ c, (∑' i : k.office c,k.fee u w B a x (k.address i)) := by
      rw [mul_sum]
      refine sum_congr rfl fun j _ => ?_
      unfold f; rw [k.price_coin h.positive]
      by_cases hx : x ∈ region j
      · rw [if_pos hx]; unfold fee locus mode; simp_rw [k.serves j]
        simp only [region] at hx; simp_rw [if_pos hx, tsum_mul_right,tsum_mul_left]
        unfold levy domain E region; ring
      rw [if_neg hx]; unfold fee locus mode; simp_rw [k.serves j]
      simp only [region] at hx; simp_rw [if_neg hx,tsum_zero,mul_zero]
    _ = 2*(∑' i,k.fee u w B a x i) := by rw [← ht.tsum_eq,tsum_fintype]
    _ ≤ 2*δ := mul_le_mul_of_nonneg_left hi.2.2 zero_le_two

lemma levy_simple (hw : ∀ i,0 < w i) (ha : 0 ≤ a) (h : k.Worth w B a u δ)
    (c : Column R n) (he : ¬ hot (domain c)) : k.levy u c ≤ δ := by
  obtain ⟨x,hx⟩ := c.1.property
  have hs := budget_single (k.payment hw ha h x) c
  change (if x∈ _ then _ else _ ) ≤ _ at hs
  rw [if_pos (show x∈region c from hx)] at hs; dsimp only at hs; rw [price_coin k h.positive,not_ne_iff.mp he,Poly.quiet_toll,one_mul] at hs
  have ht : 1 ≤ Real.exp (a*↑(coverNumber B (region c))) := Real.one_le_exp (by positivity)
  calc
    k.levy u c ≤ k.levy u c * Real.exp (a*↑(coverNumber B (region c))) := le_mul_of_one_le_right (tsum_nonneg fun _ => h.positive _) ht
    _ ≤ δ := by linarith

lemma funded (hw : ∀ i,0 < w i) (ha : 0 ≤ a) (he : δ ≤ 1) (h : k.Worth w B a u δ) (c : Column R n) (U) :
    Width.Covered (k.slip c U) (k.coin u c) := by
  have hh := (h.usage ha hw U).comp_injective (k.address_inj c)
  have hr := (h.enough ha hw).comp_injective (k.address_inj c)
  have ho : ‖k.row c U‖ ≤ k.levy u c := (norm_tsum_le_tsum_norm hh).trans (hh.tsum_le_tsum (fun i => h.always _ U) hr)
  have hm : 0 ≤ k.levy u c := (norm_nonneg _).trans ho
  have hs (z : R.Mode) (x : ℂ) (he : ‖x‖ ≤ 2*k.levy u c) : Width.Covered (Poly.send z x) (Poly.send z (↑(2*k.levy u c) : ℂ)) := by
    intro i; by_cases Hi : i=z
    · subst i; rw [Poly.part_send,if_pos rfl,Poly.part_send,if_pos rfl]; exact ⟨he,rfl⟩
    rw [Poly.part_send,if_neg Hi, Poly.part_send,if_neg Hi]; simp
  unfold slip coin; split
  · exact hs _ _ (ho.trans (by linarith))
  next h' =>
    rw [show domain c = R.quiet from not_ne_iff.mp h']
    refine hs _ _ ?_
    have hl := k.levy_simple hw ha h c h'
    have H := (Complex.abs_re_le_norm _).trans ho
    have hR := Real.abs_exp_sub_one_le (x := (k.row c U).re) (H.trans (hl.trans he))
    norm_cast
    rw [Real.norm_eq_abs]
    linarith

/-- stand-alone arbitrary letter orchestra (a few finite supports but ALL
weights evaluated with the stated exponential); used also for covered norms
on a family of held test arguments with the same u. -/
lemma receipt (hw : ∀ i,0 < w i) (ha : 0 ≤ a) (he : δ ≤ 1) (h : k.Worth w B a u δ) :
    Hit region B (fun c => Poly.price w (k.coin u c)) a (2*δ) ∧
      ∀ c U, Width.Covered (k.slip c U) (k.coin u c) := ⟨k.payment hw ha h,k.funded hw ha he h⟩

end YM.RG3.Forms.Feed
