import YM.RG03.Attach.Poly
import YM.Extra.MULTISOURCE_TRAJECTORIES.Algebra

/-! # Exact and priced logarithmic corrections
Correction = (real vacuum exponential × marker exponential) − 1. Every nontrivial
product with a compulsory old carrier will pay one forced fugacity (Budget file);
correction hits at the stronger exponent can be verified from the log hits,
independently of the number of markers. No volume or sup-to-l1 conversion. -/

set_option autoImplicit false
noncomputable section
namespace YM.RG03
open RG Lattice Wilson Function Marker Filter Finset
open scoped Topology BigOperators Classical
variable {V : Type*} [DecidableEq V] {R : Census V}

lemma price_neg (x : Poly R) (w : V → ℝ) : Poly.price w (-x)=Poly.price w x := by simp [Poly.price]

lemma price_sub (x y : Poly R) {w : V → ℝ} (hw : ∀ i,0<w i) : Poly.price w (x-y)≤Poly.price w x+Poly.price w y := by
  rw [sub_eq_add_neg]
  exact price_neg y w ▸ Poly.addition hw x (-y)

variable [Fintype V]

def liftExp (a : ℝ) (x : Poly R) : Poly R := (Real.exp a : ℂ) • Poly.pass x

theorem liftExp_cont : Continuous (fun p : ℝ × Poly R=>liftExp p.1 p.2) := by
  unfold liftExp; fun_prop

theorem liftExp_of_sum (a b : ℝ) {x y : Poly R} (hx : x.part R.quiet=0) (hy : y.part R.quiet=0) :
    liftExp (a+b) (x+y) = liftExp a x * liftExp b y := by
  unfold liftExp
  rw [Real.exp_add,Complex.ofReal_mul,Extra.Trajectories.pass_add hx hy, ← Poly.product_bead, ← Poly.product_bead,
    ← Poly.product_bead,map_mul]; ring

theorem liftExp_nil : liftExp (R:=R) 0 0 =1 := by
  unfold liftExp; rw [Real.exp_zero,Complex.ofReal_one, Extra.Trajectories.pass_zero,one_smul]

lemma liftExp_total {α : Type*} (s : Finset α) (a : α → ℝ) (x : α → Poly R) (h : ∀ i∈s, (x i).part R.quiet=0) :
    liftExp (∑ i∈s,a i) (∑ i∈s,x i)=∏ i∈s,liftExp (a i) (x i) := by
  induction s using Finset.induction_on with
  | empty => simpa only [sum_empty,prod_empty] using liftExp_nil
  | insert i t hi ih =>
    have he j (hj:j∈t):= h j (mem_insert_of_mem hj)
    rw [sum_insert hi,sum_insert hi,prod_insert hi,liftExp_of_sum _ _ (h i (mem_insert_self ..)) (by
      rw [Poly.part_sum]; exact sum_eq_zero he),ih he]

lemma liftExp_hasProd {α : Type*} (a : α → ℝ) (x : α → Poly R) (h : ∀ i, (x i).part R.quiet=0)
    (ha : Summable a) (hx : Summable x) :
    HasProd (fun i=>liftExp (a i) (x i)) (liftExp (∑' i,a i) (∑' i,x i)) := by
  unfold HasProd
  simp_rw [← liftExp_total (h:=fun i _=>h i)]
  exact (liftExp_cont.tendsto _).comp (ha.hasSum.prodMk_nhds hx.hasSum)

def charge (a : ℝ) (x : Poly R) := liftExp a x - 1

/-- no census-card payment from the nilpotent exponential -/
lemma price_pass_rest (x : Poly R) {r : V → ℝ} (hr : ∀ i,0<r i) :
    Poly.price r (Poly.pass x - 1) ≤ Real.exp (Poly.price r x)-1 := by
  let v:=Poly.price r x; have hv:0≤v:=Poly.nonnegative hr _
  have H : HasSum (fun i : ℕ=>v^i/i.factorial) (Real.exp v) := by
    convert! NormedSpace.expSeries_div_hasSum_exp v using 1
    rw [Real.exp_eq_exp_ℝ]
  have h (i : ℕ) : Poly.price r ((i.factorial:ℂ)⁻¹ • x^i) ≤ v^i/i.factorial := by
    rw [Poly.adapted]
    exact (mul_le_mul_of_nonneg_left (Poly.powers hr _ _) (norm_nonneg _)).trans_eq (by simp [v,div_eq_mul_inv,mul_comm])
  unfold Poly.pass; rw [sum_range_succ']; simp only [Nat.factorial_zero, Nat.cast_one, inv_one,pow_zero,one_smul, add_sub_cancel_right]
  apply (Poly.batch hr ..).trans
  apply (sum_le_sum fun i _ => h (i+1)).trans
  rw [le_sub_iff_add_le,show (1:ℝ)=v^0/Nat.factorial 0 by simp,← sum_range_succ' (fun k : ℕ => v^k/k.factorial)]
  rw [← H.tsum_eq]; exact H.summable.sum_le_tsum _ fun i _=> by positivity

lemma charge_split (a : ℝ) (x : Poly R) : charge a x =
    (Real.exp a : ℂ) • (Poly.pass x - 1) + ((Real.exp a-1:ℝ):ℂ) • (1:Poly R) := by
  unfold charge liftExp; rw [smul_sub,Complex.ofReal_sub,Complex.ofReal_one,sub_smul,one_smul]; abel

lemma charge_price (a : ℝ) (x : Poly R) {r : V → ℝ} (hr : ∀ i,0<r i) (ha : |a|≤1) (hx : Poly.price r x≤1) :
    Poly.price r (charge a x) ≤ 2*Real.exp 1*Poly.price r x+2*|a| := by
  rw [charge_split]; apply (Poly.addition hr ..).trans
  simp only [Poly.adapted,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos a),Poly.one_price,mul_one]
  apply add_le_add _ (Real.abs_exp_sub_one_le ha)
  let v:=Poly.price r x; have hv:0≤v:=Poly.nonnegative hr _
  calc
    _ ≤ Real.exp 1 * (2*v) := mul_le_mul (Real.exp_le_exp.mpr (le_of_abs_le ha))
      ((price_pass_rest x hr).trans ((abs_le.mp (Real.abs_exp_sub_one_le (by rwa [abs_of_nonneg hv]))).2.trans_eq (by rw [abs_of_nonneg hv])))
      (Poly.nonnegative hr _) (Real.exp_pos _).le
    _ = _ := by ring

lemma charge_series {a : ℕ→ℝ} {x : ℕ→Poly R} {r : V→ℝ} (hr : ∀ i,0<r i)
    (ha : Summable fun i=>|a i|) (hx : Summable fun i=>Poly.price r (x i)) :
    Summable fun i=> Poly.price r (charge (a i) (x i)) := by
  refine Summable.of_norm_bounded_eventually_nat ((hx.mul_left (2*Real.exp 1)).add (ha.mul_left 2)) ?_
  filter_upwards [ha.tendsto_atTop_zero.eventually_le_const zero_lt_one,hx.tendsto_atTop_zero.eventually_le_const zero_lt_one] with i hi hI
  rw [Real.norm_of_nonneg (Poly.nonnegative hr _)]
  exact charge_price (a i) (x i) hr hi hI
end YM.RG03
