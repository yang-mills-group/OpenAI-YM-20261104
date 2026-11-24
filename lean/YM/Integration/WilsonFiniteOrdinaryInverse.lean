import YM.Integration.WilsonFiniteOrdinaryWindow
import YM.Comparison.RG02.Order.Pay

/-! A source-weighted allowance for the pre-filed inverse ordinary table
at the authentic upper coupling. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonFiniteOrdinaryInverse
open Finset Marker Multi Comparison.RG02 Comparison.RG02.Order Comparison.RG02.Cumulants
open Primitives.GCC.Anchor WilsonIndependentOrdinaryPairGrade WilsonFiniteOrdinaryPartitions
open scoped BigOperators Classical
variable {V : Type} [Fintype V] [DecidableEq V] {J : Census V} {r : ℕ}

def room (J : Census V) : ℝ := ∑ s : J.Mode,2*((shards J s).card:ℝ)
def fee (J : Census V) : ℝ := ∑ n∈range (Fintype.card V+1),(1+room J)^n

omit [Fintype V] in
theorem scaled (g : ℝ) (w : V → ℝ) (s : J.Mode) :
    Poly.toll (fun v => g*w v) s=g^s.val.card*Poly.toll w s := by
  simp only [Poly.toll,prod_mul_distrib,prod_const]

theorem ordinary (W : Grade J r) (unit : UnitLeading W) (sym : Symmetric W)
    (w : V → ℝ) (hw : ∀ j,0<w j) (g : ℝ) (gp : 0<g) (small : g≤1)
    (paid : ∀ s : J.Mode,g*(Poly.toll w s*mass (slot s (render (logMarked W))))≤1)
    (s : J.Mode) :
    Poly.toll (fun v => g*w v) s*‖(value (g:ℂ) (ratio W)).part s‖ ≤ 2*((shards J s).card:ℝ) := by
  let u := fun v => g*w v
  let C := render (logMarked W)
  let T := value (g:ℂ) (logMarked W)
  have hu (v : V) : 0<u v := mul_pos gp (hw _)
  have gz : ‖(g:ℂ)‖≤1 := by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos gp]; exact small
  let price (t : Hot J) := Poly.toll u t.val * mass (slot t.val C)
  have nonneg (t : Hot J) : 0≤price t := mul_nonneg (Poly.worth hu _).le (IterationFour.Series.mass_nn _)
  have one (t : Hot J) : price t≤1 := by
    have n : g^t.val.val.card ≤ g := (pow_le_pow_of_le_one gp.le small (card_pos.mpr t.property : 1≤t.val.val.card)).trans_eq (pow_one _)
    dsimp only [price,u,C]
    rw [scaled,mul_assoc]
    exact (mul_le_mul_of_nonneg_right n (mul_nonneg (Poly.worth hw _).le (IterationFour.Series.mass_nn _))).trans (paid _)
  have cluster (q : (parts J).Mode) : (∏ t ∈ q.val,price t) ≤ 1 := by
    exact (prod_le_prod (fun t _ => nonneg t) (fun t _=>one t)).trans_eq (by simp)
  have summed : (∑ q∈shards J s, ∏ t∈q.val,price t) ≤ ((shards J s).card:ℝ) :=
    (sum_le_sum (fun q _ => cluster q)).trans_eq (by simp)
  have uncut : Poly.toll u s * ‖(Poly.pass T).part s‖ ≤ ((shards J s).card:ℝ) := by
    rw [←evaluated W unit (g:ℂ) s,WilsonFiniteOrdinaryPartitions.ordinary,Polynomial.eval_finsetSum]
    apply (mul_le_mul_of_nonneg_left (norm_sum_le ..) (Poly.worth hu _).le).trans
    rw [mul_sum]
    apply (sum_le_sum (fun q h => ?_)).trans summed
    rw [Polynomial.eval_prod,norm_prod,WilsonFiniteOrdinaryTail.toll u s q h,←prod_mul_distrib]
    exact prod_le_prod (fun t _=>mul_nonneg (Poly.worth hu _).le (norm_nonneg _))
      (fun t _=>mul_le_mul_of_nonneg_left (IterationFour.Series.cash_value _ gz) (Poly.worth hu _).le)
  have tail := WilsonFiniteOrdinaryTail.priced W unit sym u hu (g:ℂ) gz s
  change Poly.toll u s*‖(Poly.pass T).part s-(value (g:ℂ) (ratio W)).part s‖ ≤
    ‖(g:ℂ)‖^(r+1)*(∑ q∈shards J s, ∏ t∈q.val,price t) at tail
  have remainder := tail.trans ((mul_le_of_le_one_left
    (sum_nonneg (fun _ _ => prod_nonneg (fun t _=> nonneg t))) (pow_le_one₀ (norm_nonneg _) gz)).trans summed)
  have ready := norm_add_le ((Poly.pass T).part s) ((value (g:ℂ) (ratio W)).part s-(Poly.pass T).part s)
  rw [show (Poly.pass T).part s + ((value (g:ℂ) (ratio W)).part s-(Poly.pass T).part s)=
      (value (g:ℂ) (ratio W)).part s from by abel,norm_sub_rev (value (g:ℂ) (ratio W) |>.part s)] at ready
  calc
    _ ≤ Poly.toll u s*(‖(Poly.pass T).part s‖+
          ‖(Poly.pass T).part s-(value (g:ℂ) (ratio W)).part s‖) :=
      mul_le_mul_of_nonneg_left ready (Poly.worth hu _).le
    _ ≤ _ := by rw [mul_add,two_mul]; exact add_le_add uncut remainder

theorem inverse (W : Grade J r) (unit : UnitLeading W) (sym : Symmetric W)
    (w : V → ℝ) (hw : ∀ j,0<w j) (g : ℝ) (gp : 0<g) (small : g≤1)
    (paid : ∀ s : J.Mode,g*(Poly.toll w s*mass (slot s (render (logMarked W))))≤1) :
    Poly.price (fun v=>g*w v) (inverseMass (value (g:ℂ) (ratio W))) ≤ fee J := by
  let Q := value (g:ℂ) (ratio W)
  let u := fun v=>g*w v
  have hu (v : V) : 0<u v := mul_pos gp (hw _)
  have unitQ : Q.part J.quiet=1 := leading_trunc_value (ratio_pure unit) _
  have bound : Poly.price u Q≤room J := sum_le_sum fun s _=> ordinary W unit sym w hw g gp small paid s
  have neg : Poly.price u (1-Q) ≤ 1+room J :=
    (priced_sub u hu 1 Q).trans (by rw [Poly.one_price]; exact add_le_add le_rfl bound)
  rw [geometric_inverse Q unitQ]
  apply (Poly.batch hu _ _).trans
  exact sum_le_sum fun n _ => (Poly.powers hu (1-Q) n).trans
    (pow_le_pow_left₀ (Poly.nonnegative hu _) neg n)

end YM.Integration.WilsonFiniteOrdinaryInverse
