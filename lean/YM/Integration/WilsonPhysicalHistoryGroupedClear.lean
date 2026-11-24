import YM.Integration.WilsonPhysicalHistoryGroupedLamps
import YM.Extra.MULTISOURCE_TRAJECTORIES.Algebra

/-! Clear regular entries of the old pupil are a genuine constant marker
polynomial. Its price follows from the original finite names and the
full-support income, even with an extensive torus. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPhysicalHistoryGroupedClear
open Finset Lattice Wilson RG Ac Marker Push AbsoluteSums QuadraticLocal MergeProof MergeProof.Accent
open WilsonPhysicalHistoryGroupedLamps
open scoped BigOperators Classical

variable {V T I : Type*} [DecidableEq V] [Fintype V] {Z : Census V} {G : Gauge} {n : Side}
  {p : BudgetPoint} {o : V → Site n} (L : Lamps T I G p o Z)
  (w : V → ℝ) (pos : ∀ v, 0 < w v)

def constant (t : T) : Poly Z := ∑' i, row L {j | L.clear j} t i 1
def localLog (t : T) (U : Config G n) : Poly Z := ∑' i, row L {j | ¬ L.clear j} t i U

omit [Fintype V] in
private theorem constant_row (t : T) (i : I) (U : Config G n) :
    row L {j | L.clear j} t i U = row L {j | L.clear j} t i 1 := by
  by_cases h : L.clear i
  · simp only [row, Set.mem_setOf_eq, if_pos h, Lamps.frame, Lamps.light, L.pure t i U h]
  · simp only [row, Set.mem_setOf_eq, if_neg h]

include pos in
omit [Fintype V] in
theorem split {B : ℕ} {a cost : ℝ} (expo : 0 ≤ a) (paid : L.Paid w B a cost)
    (t : T) (U : Config G n) : L.log t U = constant L t + localLog L t U := by
  have sums (entries : Set I) (W : Config G n) :=
    (Towed.repair (stored L w pos entries expo paid t) pos W).2
  unfold Lamps.log constant localLog
  rw [← (sums {j | L.clear j} 1).tsum_add (sums {j | ¬ L.clear j} U)]
  apply tsum_congr
  intro i
  rw [← constant_row L t i U]
  by_cases h : L.clear i <;> simp [row, h]

include pos in
theorem factored {B : ℕ} {a cost : ℝ} (expo : 0 ≤ a) (paid : L.Paid w B a cost)
    (t : T) (U : Config G n) :
    Poly.pass (L.log t U) = Poly.pass (constant L t) * Poly.pass (localLog L t U) := by
  have quiet (entries : Set I) (W : Config G n) :
      (∑' i, row L entries t i W).part Z.quiet=0 := by
    rw [Poly.share ((Towed.repair (stored L w pos entries expo paid t) pos W).2) _]
    calc
      _ = ∑' _ : I, (0:ℂ) := by
        apply tsum_congr
        intro i
        by_cases h : i ∈ entries <;> simp [row, h]
      _ = 0 := tsum_zero
  rw [split L w pos expo paid t U]
  exact Extra.Trajectories.pass_add (quiet _ 1) (quiet _ U)

include pos in
theorem priced {B : ℕ} {a cost : ℝ} (expo : 0 ≤ a) (paid : L.Paid w B a cost)
    (t : T) : Poly.price w (constant L t) ≤ (Fintype.card V : ℝ)*cost := by
  obtain ⟨cap, nonnegative, protects, funded⟩ := paid.budget
  let fare (v : V) (i : I) := if o v ∈ L.ground i then
    Poly.toll w (L.mode i)*cap i * Real.exp (a*coverNumber B (L.ground i)) else 0
  have all := budget_over univ fare (fun _ => cost) (fun v _ => funded (o v))
  rw [sum_const, card_univ, nsmul_eq_mul] at all
  have received : SumBudget (fun i => Poly.price w (row L {j | L.clear j} t i 1))
      ((Fintype.card V:ℝ)*cost) := by
    refine budget_mono all (fun i => Poly.nonnegative pos _) ?_
    intro i
    obtain ⟨v, occupied⟩ := nonempty_iff_ne_empty.mpr
      (fun h : (L.mode i).val=∅ => L.live i (Subtype.ext h))
    have on := L.roots i v occupied
    have local_bound := L.light_size i t (1:Config G n)
      (protects i t (L.address i).site (L.address i).anchor)
    refine le_trans (b:=fare v i) ?_ (single_le_sum (f:=fun v => fare v i)
      (fun v _ => (funded (o v)).1 i) (mem_univ v))
    by_cases clear : L.clear i
    · rw [show row L {j | L.clear j} t i 1=L.frame i t 1 from if_pos clear]
      change Poly.price w (L.frame i t 1) ≤ if o v ∈ L.ground i then _ else 0
      have place : o v ∈ L.ground i := on
      rw [if_pos place, Lamps.frame, Poly.solo]
      exact (mul_le_mul_of_nonneg_left local_bound (Poly.worth pos _).le).trans
        (le_mul_of_one_le_right (mul_nonneg (Poly.worth pos _).le (nonnegative i))
          (Real.one_le_exp (mul_nonneg expo (Nat.cast_nonneg _))))
    · simp only [row, Set.mem_setOf_eq, if_neg clear, Poly.zero_price]
      exact (funded (o v)).1 i
  exact (Poly.budgeted pos received.2.1 (fun i => le_rfl)).2.trans received.2.2

end YM.Integration.WilsonPhysicalHistoryGroupedClear
end
