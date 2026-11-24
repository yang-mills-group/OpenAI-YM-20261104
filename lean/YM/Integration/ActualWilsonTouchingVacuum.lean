import YM.Integration.CoveredOrdinaryMinor
import YM.Push.ABSOLUTE_SUMS.Product

/-! Rooted products of the original Wilson vacuum activities that touch one
designated Taylor support. The bound uses the per-site native budget. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualWilsonTouchingVacuum
open Finset Lattice RG Wilson Push.AbsoluteSums
open scoped BigOperators Classical

variable {ι : Type*} {n : Side}

def touch (D : ι → Support n) (Y : Support n) (f : ι → ℝ) (j : ι) : ℝ :=
  if ¬Disjoint (D j) Y then f j else 0

/-- One unit of the per-site invoice pays for each touching partner. -/
theorem charges (D : ι → Support n) (Y : Support n) {f : ι → ℝ} {w : ℝ}
    (hf : ∀ j, 0 ≤ f j) (hw : ∀ x : Site n,
      SumBudget (fun j => if x ∈ D j then f j else 0) w) :
    SumBudget (touch D Y f) (Y.card*w) := by
  let site (x : Site n) (j : ι) := if x ∈ D j then f j else 0
  have hs (x : Site n) (j : ι) : 0 ≤ site x j := (hw x).1 j
  have h0 (j : ι) : 0 ≤ touch D Y f j := by
    unfold touch
    split
    · exact hf j
    exact le_rfl
  have h1 (j : ι) : touch D Y f j ≤ ∑ x ∈ Y, site x j := by
    unfold touch
    split
    next h =>
      obtain ⟨x,hx,hY⟩ := Finset.not_disjoint_iff.1 h
      have hx' := Finset.single_le_sum (f := fun t => site t j) (fun x _ => hs x j) hY
      simpa only [site,if_pos hx] using hx'
    exact Finset.sum_nonneg (fun x _ => hs x j)
  apply budget_of_sum h0
  intro I
  calc
    _ ≤ ∑ j ∈ I, ∑ x ∈ Y, site x j := Finset.sum_le_sum fun j _ => h1 j
    _ = ∑ x ∈ Y, ∑ j ∈ I, site x j := Finset.sum_comm
    _ ≤ ∑ _x ∈ Y, w := Finset.sum_le_sum fun x _ => budget_sum (hw x) I
    _ = _ := by simp only [sum_const,nsmul_eq_mul]

/-- Each attached support intersects the designated support. -/
theorem cover (D : ι → Support n) (Y : Support n) (I : Finset ι) (B : ℕ)
    (h : ∀ j ∈ I, ¬Disjoint (D j) Y) :
    coverNumber B (Y ∪ I.biUnion D) ≤ coverNumber B Y + ∑ j ∈ I, coverNumber B (D j) := by
  induction I using Finset.induction_on with
  | empty => simp
  | @insert j I hj ih =>
    rw [biUnion_insert,sum_insert hj,Finset.union_left_comm]
    obtain ⟨x,hx,hY⟩ := Finset.not_disjoint_iff.1 (h j (mem_insert_self ..))
    have hcard := ih (fun j hj => h j (mem_insert_of_mem hj))
    exact (Corona.meets_sum hx (show x ∈ Y ∪ I.biUnion D from mem_union_left _ hY) B).trans (by omega)

/-- The signed field in a joined slot has exactly the product of its native
vacuum majorants. -/
def invoice (p : BudgetPoint) (D : ι → Support n) (Y : Support n) (b : ι → ℝ) (I : Finset ι) :=
  if ∀ j ∈ I, ¬Disjoint (D j) Y then p.mass (Y ∪ I.biUnion D) (∏ j ∈ I, b j) else 0

theorem products (p : BudgetPoint) (D : ι → Support n) (Y : Support n) {b : ι → ℝ} {w : ℝ}
    (hb : ∀ j, 0 ≤ b j)
    (hw : ∀ x : Site n, SumBudget (fun j => if x ∈ D j then p.mass (D j) (b j) else 0) w) :
    SumBudget (invoice p D Y b) (Real.exp (p.supportExponent*coverNumber p.B Y+Y.card*w)) := by
  let f j := p.mass (D j) (b j)
  have hf (j) : 0 ≤ f j := (hb j).trans (p.loMass _ _ (hb j))
  have H := Product.set_products (charges D Y hf hw)
  have hscaled := budget_scale (Real.exp_pos (p.supportExponent*coverNumber p.B Y)).le H
  rw [← Real.exp_add] at hscaled
  apply budget_mono hscaled
  · intro I
    unfold invoice
    split
    · exact mul_nonneg (Real.exp_pos _).le (Finset.prod_nonneg fun j _ => hb j)
    exact le_rfl
  intro I
  unfold invoice
  split
  next h =>
    have same : (∏ j ∈ I, touch D Y f j) = ∏ j ∈ I, f j :=
      Finset.prod_congr rfl (fun j hj => if_pos (h j hj))
    rw [same]
    have he : (coverNumber p.B (Y ∪ I.biUnion D) : ℝ) ≤ coverNumber p.B Y +
        ∑ j ∈ I, (coverNumber p.B (D j) : ℝ) := by exact_mod_cast cover D Y I p.B h
    dsimp only [f,BudgetPoint.mass]
    rw [Finset.prod_mul_distrib,← Real.exp_sum,← Finset.mul_sum,← mul_assoc,← Real.exp_add,← mul_add]
    exact mul_le_mul_of_nonneg_right (Real.exp_monotone (mul_le_mul_of_nonneg_left he p.exponent_pos.le))
      (Finset.prod_nonneg fun j _ => hb j)
  exact mul_nonneg (Real.exp_pos _).le (H.1 I)

/-- One spare unit of the Taylor support exponent pays every touching subset
on the original per-site Wilson activity budget. -/
theorem native {G : Gauge} (W : Rep G n) {w : ℝ} (hW : W.activities.KBound W.p w)
    (hw : w * (((W.p.B+W.p.B+1 : ℕ) : ℝ)^4) ≤ 1) :
    ∃ b : ℕ → ℝ, (∀ j, 0 ≤ b j ∧ ∀ U, ‖W.activities.K j U‖ ≤ b j) ∧
      ∀ Y : Support n, SumBudget (invoice W.p (fun j => (W.activities.forced j).support) Y b)
        (Real.exp ((W.p.supportExponent+1)*coverNumber W.p.B Y)) := by
  obtain ⟨b,hb,hit⟩ := hW
  refine ⟨b,hb,fun Y => ?_⟩
  have H := products W.p (fun j => (W.activities.forced j).support) Y (fun j => (hb j).1) hit
  refine ⟨H.1,H.2.1,H.2.2.trans (Real.exp_monotone ?_)⟩
  have hsite : (Y.card : ℝ) ≤ (coverNumber W.p.B Y : ℝ) * (((W.p.B+W.p.B+1 : ℕ) : ℝ)^4) := by
    exact_mod_cast Corona.pays Y W.p.B
  have hw0 : 0 ≤ w := budget_nonneg (hit 0)
  have hvol := mul_le_mul_of_nonneg_right hsite hw0
  have hunit := mul_le_mul_of_nonneg_left hw (Nat.cast_nonneg (coverNumber W.p.B Y))
  linarith only [hvol,hunit]

end YM.Integration.ActualWilsonTouchingVacuum
