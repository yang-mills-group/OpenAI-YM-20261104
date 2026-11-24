import YM.Integration.FVA1Physical.Wilson.WickPairDifference
import YM.Comparison.RG02.Order.Pay

/-! Degree and weighted Lipschitz fees for the actual finite marker
exponential before applying the conditional Gaussian. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Finset RG Marker Comparison.RG02 Comparison.RG02.Valence Comparison.RG02.Order
open scoped Classical BigOperators
variable {V E:Type} [Fintype V] [DecidableEq V] {R:Census V} [NormedAddCommGroup E] [NormedSpace ℝ E]
def TableDegree (d:ℕ) (X:E→Poly R):Prop := ∀m:R.Mode,Level (d:ℤ) (fun z=>(X z).part m)

omit [Fintype V] in
theorem table_product_degree {a b:ℕ} {X Y:E→Poly R} (hx:TableDegree a X) (hy:TableDegree b Y) :
    TableDegree (a+b) (fun z=>X z*Y z) := by
  intro m;simp_rw [Poly.part_mul]
  apply Level.total;intro i _;apply Level.total;intro j _
  by_cases h:Poly.merges i j m
  · simp only [if_pos h,Nat.cast_add];exact (hx i).mul (hy j)
  · simp only [if_neg h];exact Level.zero _

omit [Fintype V] in
theorem table_power_degree {d:ℕ} {X:E→Poly R} (hx:TableDegree d X) (k:ℕ) :
    TableDegree (k*d) (fun z=>(X z)^k) := by
  induction k with
  | zero => intro m;simp only [zero_mul,pow_zero,Nat.cast_zero];exact Level.constant _
  | succ k ih => simpa only [Nat.succ_mul,pow_succ] using table_product_degree ih hx

theorem table_pass_degree {d:ℕ} {X:E→Poly R} (hx:TableDegree d X) :
    TableDegree (Fintype.card V*d) (fun z=>Poly.pass (X z)) := by
  intro m;simp_rw [Poly.pass,Poly.part_sum,Poly.part_smul]
  apply Level.total;intro k hk
  have h:k≤Fintype.card V:=Nat.le_of_lt_succ (mem_range.mp hk)
  apply ((table_power_degree hx k m).factor ((k.factorial:ℂ)⁻¹)).promote
  exact_mod_cast Nat.mul_le_mul_right d h

def passSlope (n:ℕ) (H:ℝ) :ℝ:=∑ i∈range n,((i+1:ℕ):ℝ)*H^i
theorem passSlope_nonnegative (n:ℕ) {H:ℝ} (hp:0≤H): 0≤passSlope n H:=
  sum_nonneg fun _ _=>mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp _)

theorem pass_difference (w:V→ℝ) (hw:∀i,0<w i) (X Y:Poly R) {H:ℝ}
    (hx:Poly.price w X≤H) (hy:Poly.price w Y≤H) :
    Poly.price w (Poly.pass X-Poly.pass Y)≤passSlope (Fintype.card V) H*Poly.price w (X-Y) := by
  let n:=Fintype.card V
  let f (k:ℕ):Poly R:=((k.factorial:ℂ)⁻¹) • (X^k-Y^k)
  have eq : Poly.pass X-Poly.pass Y=∑ i∈range n,f (i+1) := by
    unfold Poly.pass;rw [←sum_sub_distrib];simp_rw [←smul_sub]
    change (∑ k∈range (n+1),f k)=_
    rw [Finset.sum_range_succ' f,show f 0=0 by simp [f],add_zero]
  rw [eq];apply (Poly.batch hw ..).trans
  unfold passSlope;rw [sum_mul];apply sum_le_sum;intro i _
  unfold f;rw [Poly.adapted]
  have h : ‖(((i+1).factorial:ℂ)⁻¹)‖≤1 := by
    rw [norm_inv,Complex.norm_natCast];exact inv_le_one_of_one_le₀ (by exact_mod_cast Nat.factorial_pos (i+1))
  exact (mul_le_of_le_one_left (Poly.nonnegative hw _) h).trans (power_price X Y w hw hx hy i)
end YM.Integration.FVA1Physical.Wilson
