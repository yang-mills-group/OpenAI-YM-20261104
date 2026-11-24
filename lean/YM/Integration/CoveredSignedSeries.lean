import YM.Integration.CoveredSignedCofactors
import YM.Integration.CoveredOrdinaryInsertion
import YM.Marker.Truncated

/-! Signed countable cofactors. Absolute convergence is derived from the
same common row majorant and exact-coverage insertion budget, before the
signed telescope is interchanged. No cofactor positivity is asserted. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.CoveredSignedSeries
open Finset Function Lattice RG Marker SectorNext.Vacuum
open Push.AbsoluteSums CoveredOrdinaryInsertion CoveredSignedCofactors
open scoped Classical BigOperators Topology
variable {V : Type*} [DecidableEq V] [Fintype V] {Γ : Census V} {n : Side}

theorem finite_fibers_budget {ι κ : Type*} (S : ι → Finset κ)
    (f : ι → κ → ℝ) (hf : ∀ i j, 0 ≤ f i j) {C : ℝ}
    (h : SumBudget (fun i => ∑ j ∈ S i, f i j) C) :
    SumBudget (fun p : ι × κ => if p.2 ∈ S p.1 then f p.1 p.2 else 0) C := by
  have hpos (p : ι × κ) : 0 ≤ if p.2 ∈ S p.1 then f p.1 p.2 else 0 := by
    split
    · exact hf _ _
    · exact le_rfl
  apply budget_of_sum hpos
  intro T
  let A := T.image Prod.fst
  let B := T.image Prod.snd
  have hsub : T ⊆ A ×ˢ B := by
    intro p hp
    exact mem_product.mpr ⟨mem_image_of_mem _ hp, mem_image_of_mem _ hp⟩
  calc
    _ ≤ ∑ p ∈ A ×ˢ B, if p.2 ∈ S p.1 then f p.1 p.2 else 0 :=
      sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => hpos p)
    _ = ∑ i ∈ A, ∑ j ∈ B, if j ∈ S i then f i j else 0 := by rw [sum_product]
    _ ≤ ∑ i ∈ A, ∑ j ∈ S i, f i j := by
      apply sum_le_sum
      intro i _
      rw [← sum_filter]
      exact sum_le_sum_of_subset_of_nonneg (fun j hj => (mem_filter.mp hj).2)
        (fun j _ _ => hf i j)
    _ ≤ C := budget_sum h A

theorem mixed_price {w : V → ℝ} (hw : ∀ v, 0 < w v)
    (F G : ℕ → Poly Γ) (b : ℕ → ℝ)
    (hF : ∀ i, Poly.price w (F i) ≤ b i)
    (hG : ∀ i, Poly.price w (G i) ≤ b i) (i : ℕ) (s : Finset ℕ) :
    Poly.price w (mixed F G i s) ≤ ∏ j ∈ s.erase i, b j := by
  let _finiteV : Fintype V := inferInstance
  apply (Poly.multiple hw (s.erase i) (fun j => if j < i then G j else F j)).trans
  apply prod_le_prod
  · intro j _
    exact Poly.nonnegative hw _
  · intro j _
    split
    · exact hG j
    · exact hF j

theorem cofactor_price {w : V → ℝ} (hw : ∀ v, 0 < w v)
    (K Z : ℕ → Support n) (hZ : ∀ i, Z i ⊆ K i) (D : Support n)
    (F G : ℕ → Poly Γ) (b : ℕ → ℝ)
    (hF : ∀ i, Poly.price w (F i) ≤ b i)
    (hG : ∀ i, Poly.price w (G i) ≤ b i) (i : ℕ) (s : Finset ℕ) :
    Poly.price w (cofactorTerm K Z D F G i s) ≤
      if accounted K Z D s ∧ i ∈ s then ∏ j ∈ s.erase i, b j else 0 := by
  by_cases hp : i ∈ s ∧ Pinned K Z D i (s.erase i)
  · have ha := (pinned_erase_iff K Z hZ D i s).mp hp
    rw [cofactorTerm, if_pos hp, if_pos ha]
    exact mixed_price hw F G b hF hG i s
  · have ha : ¬ (accounted K Z D s ∧ i ∈ s) :=
      fun h => hp ((pinned_erase_iff K Z hZ D i s).mpr h)
    rw [cofactorTerm, if_neg hp, if_neg ha, Poly.zero_price]

theorem cofactor_budget {w : V → ℝ} (hw : ∀ v, 0 < w v)
    (K Z : ℕ → Support n) (hZ : ∀ i, Z i ⊆ K i)
    (hn : ∀ i, (Z i).Nonempty) {q : ℝ} (hq : q ≤ 1)
    (F G : ℕ → Poly Γ) (b : ℕ → ℝ)
    (hF : ∀ i, Poly.price w (F i) ≤ b i)
    (hG : ∀ i, Poly.price w (G i) ≤ b i)
    (hit : ∀ x : Site n, ∀ I : Finset ℕ,
      (∑ i ∈ I, if x ∈ Z i then b i else 0) ≤ q)
    (D : Support n) (i : ℕ) :
    SumBudget (fun s : Finset ℕ => Poly.price w (cofactorTerm K Z D F G i s)) 1 := by
  let e (j : ℕ) : ℝ := if j = i then 1 else 0
  have he : SumBudget e 1 := by
    apply budget_of_sum
    · intro j
      dsimp only [e]
      split <;> norm_num
    · intro s
      dsimp only [e]
      rw [sum_ite_eq']
      split <;> norm_num
  have H := insertion_budget K Z hZ hn hq b
    (fun j => (Poly.nonnegative hw (F j)).trans (hF j)) hit e he D
  have hinst : (fun a b : ℕ => Classical.propDecidable (a = b)) =
      instDecidableEqNat := Subsingleton.elim _ _
  rw [hinst] at H
  apply budget_mono H (fun _ => Poly.nonnegative hw _)
  intro s
  have hc := cofactor_price hw K Z hZ D F G b hF hG i s
  have heq : (if accounted K Z D s then
      ∑ j ∈ s, e j * ∏ k ∈ s.erase j, b k else 0) =
      if accounted K Z D s ∧ i ∈ s then ∏ j ∈ s.erase i, b j else 0 := by
    simp only [e, ite_mul, one_mul, zero_mul, sum_ite_eq']
    by_cases ha : accounted K Z D s <;> by_cases hi : i ∈ s <;> simp [ha, hi]
  exact hc.trans_eq heq.symm

theorem joint_budget {w : V → ℝ} (hw : ∀ v, 0 < w v)
    (K Z : ℕ → Support n) (hZ : ∀ i, Z i ⊆ K i)
    (hn : ∀ i, (Z i).Nonempty) {q ε : ℝ} (hq : q ≤ 1)
    (F G : ℕ → Poly Γ) (b : ℕ → ℝ)
    (hF : ∀ i, Poly.price w (F i) ≤ b i)
    (hG : ∀ i, Poly.price w (G i) ≤ b i)
    (hit : ∀ x : Site n, ∀ I : Finset ℕ,
      (∑ i ∈ I, if x ∈ Z i then b i else 0) ≤ q)
    (tail : SumBudget (fun i => Poly.price w (F i - G i)) ε) (D : Support n) :
    SumBudget (fun p : Finset ℕ × ℕ =>
      Poly.price w ((F p.2 - G p.2) * cofactorTerm K Z D F G p.2 p.1)) ε := by
  have hb j : 0 ≤ b j := (Poly.nonnegative hw (F j)).trans (hF j)
  let f (s : Finset ℕ) (i : ℕ) := if accounted K Z D s then
    Poly.price w (F i - G i) * ∏ j ∈ s.erase i, b j else 0
  have hf (s : Finset ℕ) (i : ℕ) : 0 ≤ f s i := by
    dsimp only [f]
    split
    · exact mul_nonneg (Poly.nonnegative hw _) (prod_nonneg fun j _ => hb j)
    · exact le_rfl
  have H : SumBudget (fun s : Finset ℕ => ∑ i ∈ s, f s i) ε := by
    have hN := insertion_budget K Z hZ hn hq b hb hit
      (fun i => Poly.price w (F i - G i)) tail D
    have hinst : (fun a b : ℕ => Classical.propDecidable (a = b)) =
        instDecidableEqNat := Subsingleton.elim _ _
    rw [hinst] at hN
    simpa only [f, sum_ite_irrel, sum_const_zero] using hN
  have Hp := finite_fibers_budget (fun s : Finset ℕ => s) f hf H
  apply budget_mono Hp (fun _ => Poly.nonnegative hw _)
  rintro ⟨s, i⟩
  have hc := (Poly.multiplication hw (F i - G i) (cofactorTerm K Z D F G i s)).trans
    (mul_le_mul_of_nonneg_left (cofactor_price hw K Z hZ D F G b hF hG i s)
      (Poly.nonnegative hw _))
  by_cases ha : accounted K Z D s <;> by_cases hi : i ∈ s <;> simpa [f, ha, hi] using hc

/-- The exact signed row telescope is absolutely summable before its order
is exchanged. The cofactor still carries the original residual coverage. -/
theorem series {w : V → ℝ} (hw : ∀ v, 0 < w v)
    (K Z : ℕ → Support n) (hZ : ∀ i, Z i ⊆ K i)
    (hn : ∀ i, (Z i).Nonempty) {q ε : ℝ} (hq : q ≤ 1)
    (F G : ℕ → Poly Γ) (b : ℕ → ℝ)
    (hF : ∀ i, Poly.price w (F i) ≤ b i)
    (hG : ∀ i, Poly.price w (G i) ≤ b i)
    (hit : ∀ x : Site n, ∀ I : Finset ℕ,
      (∑ i ∈ I, if x ∈ Z i then b i else 0) ≤ q)
    (tail : SumBudget (fun i => Poly.price w (F i - G i)) ε) (D : Support n) :
    (∀ i, Summable (cofactorTerm K Z D F G i)) ∧
    Summable (fun i => (F i - G i) * ∑' s, cofactorTerm K Z D F G i s) ∧
    (∑' s : Finset ℕ, if accounted K Z D s then
      (∏ i ∈ s, F i) - ∏ i ∈ s, G i else 0) =
      ∑' i, (F i - G i) * ∑' s, cofactorTerm K Z D F G i s := by
  have hs (i : ℕ) : Summable (cofactorTerm K Z D F G i) := by
    have H := cofactor_budget hw K Z hZ hn hq F G b hF hG hit D i
    exact (Poly.budgeted hw H.2.1 (fun _ => le_rfl)).1
  let f (s : Finset ℕ) (i : ℕ) := (F i - G i) * cofactorTerm K Z D F G i s
  have hf : Summable (Function.uncurry f) := by
    have H := joint_budget hw K Z hZ hn hq F G b hF hG hit tail D
    exact (Poly.budgeted hw H.2.1 (fun _ => le_rfl)).1
  letI : IsTopologicalSemiring (Poly Γ) :=
    { toContinuousAdd := inferInstance, toContinuousMul := inferInstance }
  have hm (i : ℕ) : (∑' s, f s i) =
      (F i - G i) * ∑' s, cofactorTerm K Z D F G i s :=
    (hs i).tsum_mul_left (F i - G i)
  refine ⟨hs, hf.prod_symm.prod.congr hm, ?_⟩
  have hfinite (s : Finset ℕ) : (∑' i, f s i) = ∑ i ∈ s, f s i := by
    apply tsum_eq_sum
    intro i hi
    simp only [f, cofactorTerm, hi, false_and, if_false, mul_zero]
  calc
    _ = ∑' s, ∑' i, f s i := by
      apply tsum_congr
      intro s
      exact (packet_difference K Z hZ D F G s).trans (hfinite s).symm
    _ = ∑' i, ∑' s, f s i := hf.tsum_comm.symm
    _ = _ := tsum_congr hm

end YM.Integration.CoveredSignedSeries
