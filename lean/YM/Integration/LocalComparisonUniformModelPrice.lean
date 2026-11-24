import YM.Integration.LocalComparisonPackets
import YM.Marker.Truncated
import YM.Push.ABSOLUTE_SUMS.Basic

/-!
The actual packet payment bounds its full physical value on every group field.
All occupied rows and their coupling factors are retained. The resulting
model bound is the literal finite marker-exponential polynomial, with the
number of markers and the supplied rank cap explicit.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.LocalComparison.MarkedPackets
open Lattice Wilson RG Marker
open Comparison.Density.RenderM
open Push.AbsoluteSums
open scoped BigOperators Classical

variable {G : Gauge} {n : Side} {V : Type} [DecidableEq V] [Fintype V]
    {R : Census V} {D : V → ComparisonDensity.Address.Orbit}
    {P : MarkedPackets D G n R} {p : BudgetPoint}
    {address : V → Support n}
    {region : Comparison.Density.Testing.Region (fun v => (D v).Mood) n}
    {w : V → ℝ} {g width budget : ℝ} {coverOffset coverSlope : ℕ}

/-- Full-root value cost, including the actual coupling norm. -/
private def valueFee (P : MarkedPackets D G n R) (w : V → ℝ)
    (g width : ℝ) (i : ℕ) : ℝ :=
  match P.packet i with
  | none => 0
  | some T => Poly.toll w (P.mode i) * ‖(g : ℂ) ^ P.power i‖ *
      T.coin * Real.exp (width * T.fall)

omit [Fintype V] in
private lemma fee_nonnegative
    (H : P.Paid p address region w g width budget coverOffset coverSlope) (i : ℕ) :
    0 ≤ valueFee P w g width i := by
  cases hi : P.packet i with
  | none => simp only [valueFee, hi, le_refl]
  | some T =>
    have hc := (H.coefficient i T hi).1
    have ht := (Poly.worth H.positive (P.mode i)).le
    simp only [valueFee, hi]
    positivity

private lemma all_fees
    (H : P.Paid p address region w g width budget coverOffset coverSlope) :
    SumBudget (valueFee P w g width) ((Fintype.card V : ℝ) * budget) := by
  have hs : SumBudget
      (fun i => ∑ v : V, if v ∈ (P.mode i).val then valueFee P w g width i else 0)
      (∑ _v : V, budget) :=
    budget_over Finset.univ
      (fun v i => if v ∈ (P.mode i).val then valueFee P w g width i else 0)
      (fun _ => budget) (fun v _ => H.roots v)
  have hdom (i : ℕ) : valueFee P w g width i ≤
      ∑ v : V, if v ∈ (P.mode i).val then valueFee P w g width i else 0 := by
    cases hi : P.packet i with
    | none => simp only [valueFee, hi, ite_self, Finset.sum_const_zero, le_refl]
    | some T =>
      have hne : (P.mode i).val ≠ ∅ := by
        intro hz
        exact P.marked i T hi (Subtype.ext hz)
      obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr hne
      calc
        _ = (if v ∈ (P.mode i).val then valueFee P w g width i else 0) :=
          (if_pos hv).symm
        _ ≤ ∑ v : V, if v ∈ (P.mode i).val then valueFee P w g width i else 0 :=
          Finset.single_le_sum
            (fun j _ => show 0 ≤ (if j ∈ (P.mode i).val then valueFee P w g width i else 0) from
              by split <;> first | exact fee_nonnegative H i | exact le_rfl)
            (Finset.mem_univ v)
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
    budget_mono hs (fee_nonnegative H) hdom

omit [DecidableEq V] [Fintype V] in
private lemma token_read_bound {k : ℕ}
    (T : Token G n (fun v => (D v).Mood) k)
    (x : TestSpace D) (hc : (∑ j, ‖T.gem j x‖) ≤ T.coin)
    (U : Config G n) : ‖T.read x U‖ ≤ T.coin * (2 : ℝ)^k := by
  have hcoord (i : Fin k) (j : G.ColorIndex) :
      |(T.path i).atSite U T.root j| ≤ 2 := by
    calc
      _ = |inner ℝ (EuclideanSpace.basisFun G.ColorIndex ℝ j)
          ((T.path i).atSite U T.root)| := by
        simp only [EuclideanSpace.basisFun_inner]
      _ ≤ _ := (abs_real_inner_le_norm _ _).trans (by
        rw [OrthonormalBasis.norm_eq_one, one_mul]
        exact Slot.eval_norm ..)
  unfold Token.read Token.touch
  calc
    _ ≤ ∑ b, ‖(↑(∏ i, (T.path i).atSite U T.root (b i)) : ℂ) * T.gem b x‖ :=
      norm_sum_le _ _
    _ ≤ ∑ b, ‖T.gem b x‖ * (2 : ℝ)^k := by
      apply Finset.sum_le_sum
      intro b _
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Finset.abs_prod]
      have hp : (∏ i : Fin k, |(T.path i).atSite U T.root (b i)|) ≤ (2 : ℝ)^k := by
        calc
          _ ≤ ∏ _i : Fin k, (2 : ℝ) :=
            Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun i _ => hcoord i (b i))
          _ = _ := by simp
      exact (mul_le_mul_of_nonneg_right hp (norm_nonneg _)).trans_eq (mul_comm _ _)
    _ = (∑ b, ‖T.gem b x‖) * (2 : ℝ)^k := (Finset.sum_mul _ _ _).symm
    _ ≤ T.coin * (2 : ℝ)^k := mul_le_mul_of_nonneg_right hc (by positivity)

omit [Fintype V] in
private lemma term_price_bound
    (H : P.Paid p address region w g width budget coverOffset coverSlope)
    (cap : ℕ) (hcap : P.rankCap ≤ cap)
    (x : IndependentTests D) (U : Config G n) (i : ℕ) :
    Poly.price w (Poly.send (P.mode i) (P.term (testInclusion D x) g U i)) ≤
      (2 : ℝ)^cap * valueFee P w g width i := by
  cases hi : P.packet i with
  | none => simp only [term, valueFee, hi, Poly.solo, norm_zero, mul_zero, le_refl]
  | some T =>
    have hc := (H.coefficient i T hi).1
    have ht := (Poly.worth H.positive (P.mode i)).le
    have hg := norm_nonneg ((g : ℂ)^P.power i)
    have hr : P.rank i ≤ cap := (P.rank_bounded i T hi).trans hcap
    have hp : (2 : ℝ)^(P.rank i) ≤ (2 : ℝ)^cap :=
      pow_le_pow_right₀ (by norm_num) hr
    have he : 1 ≤ Real.exp (width * T.fall) :=
      Real.one_le_exp (mul_nonneg H.width_pos.le (Nat.cast_nonneg _))
    have hv := token_read_bound T (testInclusion D x) ((H.coefficient i T hi).2 x) U
    simp only [term, valueFee, hi, Poly.solo, norm_mul]
    calc
      _ ≤ Poly.toll w (P.mode i) *
          (‖(g : ℂ)^P.power i‖ * (T.coin * (2 : ℝ)^(P.rank i))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hv hg) ht
      _ ≤ Poly.toll w (P.mode i) *
          (‖(g : ℂ)^P.power i‖ * (T.coin * (2 : ℝ)^cap)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp hc) hg) ht
      _ = (2 : ℝ)^cap *
          (Poly.toll w (P.mode i) * ‖(g : ℂ)^P.power i‖ * T.coin) := by ring
      _ ≤ (2 : ℝ)^cap *
          (Poly.toll w (P.mode i) * ‖(g : ℂ)^P.power i‖ *
            T.coin * Real.exp (width * T.fall)) :=
        mul_le_mul_of_nonneg_left
          (le_mul_of_one_le_right (mul_nonneg (mul_nonneg ht hg) hc) he)
          (by positivity)

/-- No volume factor: only the finite marker count and fixed rank cap. -/
def uniformReadCost (cap marks : ℕ) (budget : ℝ) : ℝ :=
  (2 : ℝ)^cap * ((marks : ℝ) * budget)

/-- The full finite exponential used by Poly.pass, without discarding any
marker coefficient or replacing it by an infinite exponential. -/
def uniformModelCost (cap marks : ℕ) (budget : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (marks + 1),
    (uniformReadCost cap marks budget)^i / (i.factorial : ℝ)

/-- The complete original countable packet series is summable and uniformly
priced on every group field, at the actual paid coupling. -/
theorem Paid.uniform_read
    (H : P.Paid p address region w g width budget coverOffset coverSlope)
    (cap : ℕ) (hcap : P.rankCap ≤ cap)
    (x : IndependentTests D) (U : Config G n) :
    Summable (fun i => Poly.send (P.mode i) (P.term (testInclusion D x) g U i)) ∧
      Poly.price w (P.read (testInclusion D x) g U) ≤
        uniformReadCost cap (Fintype.card V) budget := by
  have hb := budget_scale (show 0 ≤ (2 : ℝ)^cap by positivity) (all_fees H)
  obtain ⟨hs, hp⟩ := Poly.budgeted H.positive hb.2.1 (term_price_bound H cap hcap x U)
  exact ⟨hs, hp.trans hb.2.2⟩

/-- The full model multiplier has a finite polynomial invoice on all fields. -/
theorem Paid.uniform_model
    (H : P.Paid p address region w g width budget coverOffset coverSlope)
    (cap : ℕ) (hcap : P.rankCap ≤ cap)
    (x : IndependentTests D) (U : Config G n) :
    Poly.price w (Poly.pass (P.read (testInclusion D x) g U)) ≤
      uniformModelCost cap (Fintype.card V) budget := by
  have hread := (H.uniform_read cap hcap x U).2
  have hn := Poly.nonnegative H.positive (P.read (testInclusion D x) g U)
  unfold Poly.pass uniformModelCost
  refine (Poly.batch H.positive _ _).trans (Finset.sum_le_sum ?_)
  intro i _
  rw [Poly.adapted]
  have hp := (Poly.powers H.positive (P.read (testInclusion D x) g U) i).trans
    (pow_le_pow_left₀ hn hread i)
  calc
    _ ≤ ‖((i.factorial : ℂ)⁻¹)‖ *
        (uniformReadCost cap (Fintype.card V) budget)^i :=
      mul_le_mul_of_nonneg_left hp (norm_nonneg _)
    _ = _ := by simp [div_eq_mul_inv, mul_comm]

end YM.Integration.LocalComparison.MarkedPackets
end
