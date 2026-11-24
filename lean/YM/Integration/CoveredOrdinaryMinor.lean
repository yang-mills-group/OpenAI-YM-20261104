import YM.SectorNext.VACUUM_NORMALIZATION.Gas
import YM.SectorNext.VACUUM_NORMALIZATION.Covered
import YM.Ac.Tree

/-!
Exact compulsory coverage with an ordinary-gas complement minor.
The denominator is the displayed ordinary gas. No identification with an
original Wilson partition or with a covered gas is assumed or concluded.
Every forced address and its complete inventory remains in the sum.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.CoveredOrdinaryMinor
open Finset Function Lattice RG SectorNext.Vacuum
open scoped Classical BigOperators Topology

variable {n : Side} {ι κ : Type*} [DecidableEq κ]

/-- Countable version of the native finite compulsory-coverage estimate. -/
theorem covered_budget (K Z : κ → Support n) {γ q : ℝ}
    (hZ : ∀ i, Z i ⊆ K i) (hn : ∀ i, (Z i).Nonempty) (hq : q ≤ 1)
    (b : κ → ℝ) (hb : ∀ i, 0 ≤ b i)
    (hit : ∀ x : Site n, ∀ I : Finset κ,
      (∑ i ∈ I, if x ∈ Z i then b i * Real.exp (γ * (Z i).card) else 0) ≤ q)
    (D : Support n) :
    RG.SumBudget (fun s : Finset κ =>
      if accounted K Z D s then ∏ i ∈ s, b i else 0)
      ((if D = ∅ then 1 else q) * Real.exp (-γ * D.card)) := by
  let f (s : Finset κ) := if accounted K Z D s then ∏ i ∈ s, b i else 0
  have hp (s) : 0 ≤ f s := by
    unfold f
    split
    · exact prod_nonneg fun i _ => hb i
    · exact le_rfl
  have hs (S : Finset (Finset κ)) :
      ∑ s ∈ S, f s ≤ (if D = ∅ then 1 else q) * Real.exp (-γ * D.card) := by
    let I := S.biUnion id
    calc
      ∑ s ∈ S, f s = ∑ s ∈ S.filter (accounted K Z D), ∏ i ∈ s, b i := by
        simp only [f, sum_filter]
      _ ≤ ∑ s ∈ I.powerset.filter (accounted K Z D), ∏ i ∈ s, b i := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro s hs
          obtain ⟨hs, hd⟩ := mem_filter.mp hs
          exact mem_filter.mpr ⟨mem_powerset.mpr (fun i hi =>
            mem_biUnion.mpr ⟨s, hs, hi⟩), hd⟩
        · exact fun s _ _ => prod_nonneg fun i _ => hb i
      _ ≤ _ := by
        have H := cover_power K Z (γ := γ) (w := q) hZ hn hq b hb (fun x L => by
          apply le_trans ?_ (hit x L)
          apply le_of_eq
          apply sum_congr rfl
          intro i _
          by_cases hx : x ∈ Z i
          · simp only [if_pos hx]
          · simp only [if_neg hx]) D I
        by_cases hD : D = ∅
        · simpa only [if_pos hD] using H
        · simpa only [if_neg hD] using H
  exact ⟨hp, summable_of_sum_le hp hs, Real.tsum_le_of_sum_le hp hs⟩

/-- The native ordinary gas is nonzero and pays an arbitrary deleted support. -/
theorem ordinary_minor (X : ι → Support n) {w : ReLog.Grid (Site n)}
    {v : ι → ℝ} {a δ : ℝ} (hn : ∀ i, (X i).Nonempty)
    (h : ReLog.Sufficient X w v a δ) (u : ι → ℝ) (hu : ∀ i, |u i| ≤ v i)
    (Q : Support n) :
    ReLog.fumes X u univ ≠ 0 ∧
      |ReLog.fumes X u (univ \ Q) / ReLog.fumes X u univ| ≤
        Real.exp (a * Q.card) := by
  have hh := ReLog.catalog hn h u hu
  have hy : ReLog.fumes X u univ ≠ 0 := by
    rw [hh.log_form]
    exact Real.exp_ne_zero _
  obtain ⟨he, hl⟩ := ReLog.omitted hn h u hu Q
  refine ⟨hy, ?_⟩
  rw [he, mul_div_cancel_left₀ _ hy, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hl.trans_eq (mul_comm _ _)))

/-- The card charge from the ordinary minor is paid before the forced cover
estimate. The rate condition retains the exact native block-volume factor. -/
theorem covered_minor_of_hit (X : ι → Support n) {w : ReLog.Grid (Site n)}
    {v : ι → ℝ} {a δ : ℝ} (hX : ∀ i, (X i).Nonempty)
    (h : ReLog.Sufficient X w v a δ) (u : ι → ℝ) (hu : ∀ i, |u i| ≤ v i)
    (K Z : κ → Support n) (hZ : ∀ i, Z i ⊆ K i)
    (hn : ∀ i, (Z i).Nonempty) (B : ℕ) (b : κ → ℝ) (hb : ∀ i, 0 ≤ b i)
    {fee γ q : ℝ} (hit : Ac.Hit K B b fee q) (hq : q ≤ 1) (hγ : 0 ≤ γ)
    (hfee : (a + γ) * (((B+B+1 : ℕ) : ℝ)^4) ≤ fee) (D : Support n) :
    RG.SumBudget (fun s : Finset κ => if accounted K Z D s then
      (∏ i ∈ s, b i) *
        |ReLog.fumes X u (univ \ s.biUnion K) / ReLog.fumes X u univ|
      else 0)
      ((if D = ∅ then 1 else q) * Real.exp (-γ * D.card)) := by
  let c (i : κ) := b i * Real.exp (a * (K i).card)
  have hc i : 0 ≤ c i := mul_nonneg (hb i) (Real.exp_pos _).le
  have hpay (x : Site n) (I : Finset κ) :
      (∑ i ∈ I, if x ∈ Z i then c i * Real.exp (γ * (Z i).card) else 0) ≤ q := by
    apply le_trans (sum_le_sum (fun i hi => ?_))
      (((hit x).2.1.sum_le_tsum I (fun i _ => (hit x).1 i)).trans (hit x).2.2)
    by_cases hx : x ∈ Z i
    · have hk := hZ i hx
      simp only [if_pos hx, if_pos hk]
      have hz : ((Z i).card : ℝ) ≤ (K i).card := by exact_mod_cast card_le_card (hZ i)
      have hcard : ((K i).card : ℝ) ≤
          (coverNumber B (K i) : ℝ) * (((B+B+1 : ℕ) : ℝ)^4) := by
        exact_mod_cast Corona.pays (K i) B
      have he : a * (K i).card + γ * (Z i).card ≤ fee * coverNumber B (K i) := by
        calc
          _ ≤ (a + γ) * (K i).card := by nlinarith [mul_le_mul_of_nonneg_left hz hγ]
          _ ≤ (a + γ) * ((coverNumber B (K i) : ℝ) * (((B+B+1 : ℕ) : ℝ)^4)) :=
            mul_le_mul_of_nonneg_left hcard (add_nonneg h.pos hγ)
          _ = ((a + γ) * (((B+B+1 : ℕ) : ℝ)^4)) * coverNumber B (K i) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right hfee (Nat.cast_nonneg _)
      dsimp only [c]
      rw [mul_assoc, ← Real.exp_add]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (hb i)
    · rw [if_neg hx]
      exact (hit x).1 i
  have H := covered_budget K Z hZ hn hq c hc hpay D
  let f (s : Finset κ) := if accounted K Z D s then
    (∏ i ∈ s, b i) *
      |ReLog.fumes X u (univ \ s.biUnion K) / ReLog.fumes X u univ| else 0
  have hp s : 0 ≤ f s := by
    unfold f
    split
    · exact mul_nonneg (prod_nonneg fun i _ => hb i) (abs_nonneg _)
    · exact le_rfl
  have hle s : f s ≤ if accounted K Z D s then ∏ i ∈ s, c i else 0 := by
    unfold f
    split
    · have hcard : ((s.biUnion K).card : ℝ) ≤ ∑ i ∈ s, ((K i).card : ℝ) := by
        exact_mod_cast (card_biUnion_le : (s.biUnion K).card ≤ ∑ i ∈ s, (K i).card)
      calc
        _ ≤ (∏ i ∈ s, b i) * Real.exp (a * (s.biUnion K).card) :=
          mul_le_mul_of_nonneg_left (ordinary_minor X hX h u hu _).2
            (prod_nonneg fun i _ => hb i)
        _ ≤ (∏ i ∈ s, b i) * Real.exp (∑ i ∈ s, a * (K i).card) := by
          apply mul_le_mul_of_nonneg_left _ (prod_nonneg fun i _ => hb i)
          apply Real.exp_le_exp.mpr
          rw [← mul_sum]
          exact mul_le_mul_of_nonneg_left hcard h.pos
        _ = _ := by rw [Real.exp_sum, ← prod_mul_distrib]
    · exact le_rfl
  have hs := H.2.1.of_nonneg_of_le hp hle
  exact ⟨hp, hs, (hs.tsum_le_tsum hle H.2.1).trans H.2.2⟩

end YM.Integration.CoveredOrdinaryMinor
