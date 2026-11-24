import YM.Integration.WilsonCapturedPrimaryOrdinaryConvolution
import YM.Integration.WilsonReceivedLogWindow

/-! The original all-face log wallet prices the complete finite predicted
pair on its literal forest, with all retained coupling grades. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryPredictionMass
open Finset Marker Laurent Comparison.RG02 Comparison.RG02.Order WilsonIndependentOrdinaryPairGrade
open scoped Classical BigOperators
variable {V : Type} [Fintype V] [DecidableEq V] {r : ℕ}
local notation "R" => Stock.census V

private theorem one {g σ w x : ℝ} (gp : 0 ≤ g) (cool : g ≤ 1) (sw : σ ≤ w) (xp : 0 ≤ x)
    (bill : g*(w*x) ≤ 1) : (σ*g^2)*x ≤ 1 := calc
  _ ≤ (w*g^2)*x := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right sw (sq_nonneg g)) xp
  _ = g*(g*(w*x)) := by ring
  _ ≤ g*1 := mul_le_mul_of_nonneg_left bill gp
  _ ≤ 1 := by rw [mul_one];exact cool

private theorem two {g σ u v a b : ℝ} (gp : 0 ≤ g) (_up : 0 ≤ u) (vp : 0 ≤ v)
    (sw : σ ≤ u*v) (ap : 0 ≤ a) (bp : 0 ≤ b) (ha : g*(u*a) ≤ 1) (hb : g*(v*b) ≤ 1) :
    (σ*g^2)*(a*b) ≤ 1 := calc
  _ ≤ ((u*v)*g^2)*(a*b) := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right sw (sq_nonneg g)) (mul_nonneg ap bp)
  _ = (g*(u*a))*(g*(v*b)) := by ring
  _ ≤ 1*1 := mul_le_mul ha hb (mul_nonneg gp (mul_nonneg vp bp)) zero_le_one
  _ = 1 := one_mul _

theorem priced (W : Grade R r) (unit : UnitLeading W) (sym : Order.Symmetric W) {g : ℝ}
    (gp : 0 < g) (cool : g ≤ 1) (w : V → ℝ) (positive : ∀v, 0<w v)
    (a b c : V) (s : (R).Mode) (diff : a≠b) (ab : s.val={a,b})
    (priced : ∀u : (R).Mode,
      g*(Poly.toll w u*mass (slot u (render (logMarked W)))) ≤ 1 ∧
      g*(Poly.toll w u*‖(value (g:ℂ) (logMarked W)).part u‖) ≤ 1) :
    let Z := value (g:ℂ) (ratio W)
    let σ := min (Poly.toll w s) (Poly.toll w ((R).fire c))
    ‖Z.part s-Z.part ((R).fire c)‖ ≤ 4/(σ*g^2) := by
  intro Z σ
  let L := value (g:ℂ) (logMarked W)
  let A := slot ((R).fire a) (render (ratio W))
  let B := slot ((R).fire b) (render (ratio W))
  have own (i : V) : Poly.toll w ((R).fire i)=w i := by
    change ∏ v∈({i}:Finset V),w v=w i
    simp
  have pair : Poly.toll w s=w a*w b := by
    change ∏ v∈s.val,w v=_
    rw [ab,prod_insert (by simpa using diff),prod_singleton]
  have protect : 0 < σ := lt_min (Poly.worth positive s) (Poly.worth positive _)
  have fee := mul_pos protect (sq_pos_of_pos gp)
  have axis (i : V) : g*(w i*mass (slot ((R).fire i) (render (ratio W)))) ≤ 1 ∧
      g*(w i*‖L.part ((R).fire i)‖) ≤ 1 := by
    simpa only [WilsonCapturedPrimaryOrdinaryConvolution.singleton W unit sym i,own,L] using priced ((R).fire i)
  have first := one gp.le cool (min_le_left (Poly.toll w s) (Poly.toll w ((R).fire c))) (norm_nonneg _) (priced s).2
  have second := one gp.le cool (min_le_right (Poly.toll w s) (Poly.toll w ((R).fire c))) (norm_nonneg _) (priced ((R).fire c)).2
  have roots : σ ≤ w a*w b := (min_le_left ..).trans_eq pair
  have third := two gp.le (positive a).le (positive b).le roots (norm_nonneg _) (norm_nonneg _) (axis a).2 (axis b).2
  have fourth := two gp.le (positive a).le (positive b).le roots
    (sum_nonneg (s:=A.support) (fun _ _ => norm_nonneg _))
    (sum_nonneg (s:=B.support) (fun _ _ => norm_nonneg _)) (axis a).1 (axis b).1
  have cg : ‖(g:ℂ)‖=g := by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos gp]
  have tail := product_price r A B (g:ℂ) (cg.le.trans cool)
  have combined := overflow W unit sym (g:ℂ) a b c s diff ab
  have e : ‖(L.part s-L.part ((R).fire c)+L.part ((R).fire a)*L.part ((R).fire b))-(Z.part s-Z.part ((R).fire c))‖ ≤ mass A*mass B := by
    rw [combined]
    exact tail.trans (mul_le_of_le_one_left (mul_nonneg (sum_nonneg fun _ _ => norm_nonneg _) (sum_nonneg fun _ _ => norm_nonneg _))
      (pow_le_one₀ (norm_nonneg _) (cg.le.trans cool)))
  have total : ‖Z.part s-Z.part ((R).fire c)‖ ≤
      ‖L.part s‖+‖L.part ((R).fire c)‖+‖L.part ((R).fire a)‖*‖L.part ((R).fire b)‖+mass A*mass B := by
    let Y := L.part s-L.part ((R).fire c)+L.part ((R).fire a)*L.part ((R).fire b)
    calc
      _ = ‖Y-(Y-(Z.part s-Z.part ((R).fire c)))‖ := by congr 1;ring
      _ ≤ ‖Y‖+_ := norm_sub_le _ _
      _ ≤ _ := add_le_add ((norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) (norm_mul ..).le)) e
  apply (le_div_iff₀ fee).mpr
  have h := mul_le_mul_of_nonneg_left total fee.le
  change (σ*g^2)*(mass A*mass B) ≤ 1 at fourth
  dsimp only [L] at third total
  nlinarith only [first,second,third,fourth,h]

end YM.Integration.WilsonCapturedPrimaryPredictionMass
