import YM.Integration.CoveredOrdinaryMinor
import YM.Push.ABSOLUTE_SUMS.Basic

/-! A distinguished perturbation row in an exactly covered packet.
The other rows still cover precisely the remaining inventory. The estimate
uses every original address, with no unrestricted-gas substitution. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.CoveredOrdinaryInsertion
open Finset Function Lattice RG SectorNext.Vacuum CoveredOrdinaryMinor
open Push.AbsoluteSums
open scoped Classical BigOperators Topology
variable {n : Side} {κ ι : Type*}

private theorem pinned_budget (K Z : κ → Support n) (hZ : ∀ i, Z i ⊆ K i)
    (b : κ → ℝ) (hb : ∀ i, 0 ≤ b i)
    (cover : ∀ D : Support n, SumBudget (fun s : Finset κ =>
      if accounted K Z D s then ∏ i ∈ s, b i else 0) 1)
    (D : Support n) (i : κ) :
    SumBudget (fun s : Finset κ => if accounted K Z D s ∧ i ∈ s then
      ∏ j ∈ s.erase i, b j else 0) 1 := by
  apply budget_of_sum
  · intro s
    split
    · exact prod_nonneg fun j _ => hb j
    · exact le_rfl
  intro S
  let T := S.filter (fun s => accounted K Z D s ∧ i ∈ s)
  let w (s : Finset κ) := if accounted K Z (D \ Z i) s then ∏ j ∈ s, b j else 0
  have ht {s : Finset κ} (hs : s ∈ T) : accounted K Z D s ∧ i ∈ s :=
    (mem_filter.mp hs).2
  have heq :
      (∑ s ∈ S, if accounted K Z D s ∧ i ∈ s then ∏ j ∈ s.erase i, b j else 0) =
        ∑ t ∈ T.image (fun s => s.erase i), w t := by
    rw [sum_image]
    · dsimp only [T]
      rw [sum_filter]
      apply sum_congr rfl
      intro s hs
      by_cases h : accounted K Z D s ∧ i ∈ s
      · have H := reaccounts K Z h.1 hZ i h.2
        have hr : accounted K Z (D \ Z i) (s.erase i) :=
          ⟨H.1, H.2.trans (by ext x; simp only [mem_sdiff])⟩
        simp only [if_pos h, w, if_pos hr]
      · simp only [if_neg h]
    · intro a ha b hb hab
      change a.erase i = b.erase i at hab
      rw [← insert_erase (ht ha).2, ← insert_erase (ht hb).2, hab]
  rw [heq]
  exact budget_sum (cover (D \ Z i)) _

/-- Compulsory coverage costs at most one after one row is pinned. -/
theorem insertion_budget (K Z : κ → Support n) (hZ : ∀ i, Z i ⊆ K i)
    (hn : ∀ i, (Z i).Nonempty) {q ε : ℝ} (hq : q ≤ 1)
    (b : κ → ℝ) (hb : ∀ i, 0 ≤ b i)
    (hit : ∀ x : Site n, ∀ I : Finset κ,
      (∑ i ∈ I, if x ∈ Z i then b i else 0) ≤ q)
    (e : κ → ℝ) (he : SumBudget e ε) (D : Support n) :
    SumBudget (fun s : Finset κ => if accounted K Z D s then
      ∑ i ∈ s, e i * ∏ j ∈ s.erase i, b j else 0) ε := by
  have cover (E : Support n) : SumBudget (fun s : Finset κ =>
      if accounted K Z E s then ∏ i ∈ s, b i else 0) 1 := by
    have h := covered_budget K Z (γ := 0) hZ hn hq b hb (by
      intro x I
      simpa only [zero_mul, Real.exp_zero, mul_one] using hit x I) E
    apply budget_loosen h
    simp only [neg_zero, zero_mul, Real.exp_zero, mul_one]
    split
    · exact le_rfl
    · exact hq
  apply budget_of_sum
  · intro s
    split
    · exact sum_nonneg fun i _ => mul_nonneg (he.1 i) (prod_nonneg fun j _ => hb j)
    · exact le_rfl
  intro S
  let I := S.biUnion id
  have hsI {s : Finset κ} (hs : s ∈ S) : s ⊆ I := fun i hi => mem_biUnion.mpr ⟨s, hs, hi⟩
  have heq :
      (∑ s ∈ S, if accounted K Z D s then ∑ i ∈ s, e i * ∏ j ∈ s.erase i, b j else 0) =
        ∑ i ∈ I, e i * (∑ s ∈ S, if accounted K Z D s ∧ i ∈ s then
          ∏ j ∈ s.erase i, b j else 0) := by
    simp only [mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro s hs
    by_cases ha : accounted K Z D s
    · simp only [ha, true_and]
      calc
        _ = ∑ i ∈ s, e i * (if i ∈ s then ∏ j ∈ s.erase i, b j else 0) := by
          apply sum_congr rfl
          intro i hi
          rw [if_pos hi]
        _ = _ := sum_subset (hsI hs) (fun i _ hi => by rw [if_neg hi, mul_zero])
    · simp only [ha, false_and, ite_false, mul_zero, sum_const_zero]
  rw [heq]
  calc
    _ ≤ ∑ i ∈ I, e i * 1 := sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (budget_sum (pinned_budget K Z hZ b hb cover D i) S) (he.1 i)
    _ = ∑ i ∈ I, e i := by simp only [mul_one]
    _ ≤ ε := budget_sum he I

/-- The ordinary complement-minor cost is charged separately to the pinned
row and to every remaining original row before applying exact coverage. -/
theorem ordinary_insertion (X : ι → Support n) {w : ReLog.Grid (Site n)}
    {v : ι → ℝ} {a δ q ε : ℝ} (hX : ∀ i, (X i).Nonempty)
    (h : ReLog.Sufficient X w v a δ) (u : ι → ℝ) (hu : ∀ i, |u i| ≤ v i)
    (K Z : κ → Support n) (hZ : ∀ i, Z i ⊆ K i)
    (hn : ∀ i, (Z i).Nonempty) (hq : q ≤ 1)
    (b e : κ → ℝ) (hb : ∀ i, 0 ≤ b i) (he : ∀ i, 0 ≤ e i)
    (hit : ∀ x : Site n, ∀ I : Finset κ,
      (∑ i ∈ I, if x ∈ Z i then b i * Real.exp (a * (K i).card) else 0) ≤ q)
    (tail : SumBudget (fun i => e i * Real.exp (a * (K i).card)) ε)
    (D : Support n) :
    SumBudget (fun s : Finset κ => if accounted K Z D s then
      (∑ i ∈ s, e i * ∏ j ∈ s.erase i, b j) *
        |ReLog.fumes X u (univ \ s.biUnion K) / ReLog.fumes X u univ| else 0) ε := by
  let c i := b i * Real.exp (a * (K i).card)
  let d i := e i * Real.exp (a * (K i).card)
  have hc i : 0 ≤ c i := mul_nonneg (hb i) (Real.exp_pos _).le
  have H := insertion_budget K Z hZ hn hq c hc hit d tail D
  apply budget_mono H
  · intro s
    split
    · exact mul_nonneg (sum_nonneg fun i _ => mul_nonneg (he i)
        (prod_nonneg fun j _ => hb j)) (abs_nonneg _)
    · exact le_rfl
  intro s
  split
  · have hcard : ((s.biUnion K).card : ℝ) ≤ ∑ i ∈ s, ((K i).card : ℝ) := by
      exact_mod_cast (card_biUnion_le : (s.biUnion K).card ≤ ∑ i ∈ s, (K i).card)
    have hm : |ReLog.fumes X u (univ \ s.biUnion K) / ReLog.fumes X u univ| ≤
        ∏ i ∈ s, Real.exp (a * (K i).card) := by
      apply (ordinary_minor X hX h u hu _).2.trans
      rw [← Real.exp_sum, ← mul_sum]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hcard h.pos)
    calc
      _ ≤ (∑ i ∈ s, e i * ∏ j ∈ s.erase i, b j) *
          (∏ i ∈ s, Real.exp (a * (K i).card)) :=
        mul_le_mul_of_nonneg_left hm (sum_nonneg fun i _ =>
          mul_nonneg (he i) (prod_nonneg fun j _ => hb j))
      _ = ∑ i ∈ s, d i * ∏ j ∈ s.erase i, c j := by
        rw [sum_mul]
        apply sum_congr rfl
        intro i hi
        have hp : (∏ j ∈ s, Real.exp (a * (K j).card)) =
            Real.exp (a * (K i).card) * ∏ j ∈ s.erase i, Real.exp (a * (K j).card) := by
          nth_rw 1 [← insert_erase hi]
          exact prod_insert (notMem_erase i s)
        rw [hp]
        dsimp only [c, d]
        rw [prod_mul_distrib]
        ring
  · exact le_rfl


/-- The remaining-row weight needed above follows from the same original
support-hit receipt; only the displayed support-card fee is spent. -/
theorem ordinary_insertion_of_hit (X : ι → Support n) {w : ReLog.Grid (Site n)}
    {v : ι → ℝ} {a δ q ε fee : ℝ} (hX : ∀ i, (X i).Nonempty)
    (h : ReLog.Sufficient X w v a δ) (u : ι → ℝ) (hu : ∀ i, |u i| ≤ v i)
    (K Z : κ → Support n) (hZ : ∀ i, Z i ⊆ K i)
    (hn : ∀ i, (Z i).Nonempty) (hq : q ≤ 1) (B : ℕ)
    (b e : κ → ℝ) (hb : ∀ i, 0 ≤ b i) (he : ∀ i, 0 ≤ e i)
    (hit : Ac.Hit K B b fee q)
    (hfee : a * (((B+B+1 : ℕ) : ℝ)^4) ≤ fee)
    (tail : SumBudget (fun i => e i * Real.exp (a * (K i).card)) ε)
    (D : Support n) :
    SumBudget (fun s : Finset κ => if accounted K Z D s then
      (∑ i ∈ s, e i * ∏ j ∈ s.erase i, b j) *
        |ReLog.fumes X u (univ \ s.biUnion K) / ReLog.fumes X u univ| else 0) ε := by
  apply ordinary_insertion X hX h u hu K Z hZ hn hq b e hb he ?_ tail D
  intro x I
  apply le_trans (sum_le_sum (fun i _ => ?_)) (budget_sum (hit x) I)
  by_cases hz : x ∈ Z i
  · have hk := hZ i hz
    simp only [if_pos hz, if_pos hk]
    have hcard : ((K i).card : ℝ) ≤
        (coverNumber B (K i) : ℝ) * (((B+B+1 : ℕ) : ℝ)^4) := by
      exact_mod_cast Corona.pays (K i) B
    apply mul_le_mul_of_nonneg_left _ (hb i)
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ a * ((coverNumber B (K i) : ℝ) * (((B+B+1 : ℕ) : ℝ)^4)) :=
        mul_le_mul_of_nonneg_left hcard h.pos
      _ = (a * (((B+B+1 : ℕ) : ℝ)^4)) * coverNumber B (K i) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hfee (Nat.cast_nonneg _)
  · rw [if_neg hz]
    exact (hit x).1 i

end YM.Integration.CoveredOrdinaryInsertion
