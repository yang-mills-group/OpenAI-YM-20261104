import YM.Integration.WilsonPositionAuxiliaryMatch

/-! Re-expansion of the independently issued position polynomial in the
Wilson variable using its own finite-torus detector. The finite bill retains
the higher coefficients of that very detector when the mesh moves. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionRawMesh
open Function Filter Finset Set Maxwell XSpace XSpace.Normalize
open FVA2 FVA2.Register FVA2.Scale XSpace.Structure1 XSpace.Cirrus
open MS MS.Land MS.Fleet
open scoped Topology BigOperators Classical
variable {G : Gauge} (Z : WilsonPrescription G) (m : Mesh) (q : ℕ)
    (d : ℕ) {n : ℕ} (φ : Test n) (v : Tags G d n)

def detector (k : Fin (q+1)) : ℝ := (PowerSeries.coeff k (Rose.chosen Z.scheme Z.criterion m)).re
def forward (x : ℝ) : ℝ := ∑ k : Fin (q+1), detector Z m q k * x^(k:ℕ)
def source (k : Fin (q+1)) : ℂ := Scale.System.positions Z.scheme Z.criterion d m k n φ v
def order {s : ℕ} (j : Fin s → Fin (q+1)) : ℕ := ∑ i,(j i : ℕ)
def word {s : ℕ} (j : Fin s → Fin (q+1)) : ℝ := ∏ i,detector Z m q (j i)
def retained (s : ℕ) (x : ℝ) : ℝ := ∑ j : Fin s → Fin (q+1),
  if order q j ≤ q then word Z m q j * x^(order q j) else 0
def raw (x : ℝ) : ℂ := ∑ s : Fin (q+1), source Z m q d φ v s * (retained Z m q s x : ℝ)
def mass : ℝ := ∑ k : Fin (q+1), |detector Z m q k|

private theorem expand (s : ℕ) (x : ℝ) : forward Z m q x ^ s =
    ∑ j : Fin s → Fin (q+1), word Z m q j * x^(order q j) := by
  calc
    _ = ∏ _ : Fin s, ∑ k : Fin (q+1), detector Z m q k * x^(k:ℕ) := by simp [forward]
    _ = ∑ j : Fin s → Fin (q+1), ∏ i, detector Z m q (j i) * x^(j i : ℕ) := Fintype.prod_sum _
    _ = _ := by simp only [word,order,Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]

private theorem summed (s : ℕ) : ∑ j : Fin s → Fin (q+1), |word Z m q j| = mass Z m q ^ s := by
  simp only [word,Finset.abs_prod]
  rw [← Fintype.prod_sum (fun (_ : Fin s) (k : Fin (q+1))=>|detector Z m q k|)]
  simp [mass]

theorem omitted (s : ℕ) (x : ℝ) (unit : |x| ≤ 1) :
    |forward Z m q x ^s - retained Z m q s x| ≤ mass Z m q ^s * |x|^(q+1) := by
  rw [expand,retained,← Finset.sum_sub_distrib,← summed,Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs ..).trans (Finset.sum_le_sum ?_)
  intro j _
  by_cases short : order q j ≤ q
  · simp only [if_pos short,sub_self,abs_zero]
    positivity
  · simp only [if_neg short,sub_zero,abs_mul,abs_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (abs_nonneg _) unit (by omega)) (abs_nonneg _)

def slope : ℝ := ∑ s : Fin (q+1), ‖source Z m q d φ v s‖*(s:ℝ)
def price : ℝ := ∑ s : Fin (q+1), ‖source Z m q d φ v s‖*mass Z m q^(s:ℕ)

private theorem lipschitz (x y : ℝ) (hx : |x| ≤ 1) (hy : |y| ≤ 1) :
    ‖WilsonPositionFiniteMSBank.finite Z m d φ v q x - WilsonPositionFiniteMSBank.finite Z m d φ v q y‖ ≤
    slope Z m q d φ v * |x-y| := by
  rw [WilsonPositionFiniteMSBank.finite, WilsonPositionFiniteMSBank.finite,← Finset.sum_sub_distrib,slope,Finset.sum_mul]
  refine (norm_sum_le ..).trans (Finset.sum_le_sum ?_)
  intro s _
  rw [← sub_mul,norm_mul,← Complex.ofReal_pow,← Complex.ofReal_pow,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  have speed := abs_pow_sub_pow_le x y (s:ℕ)
  have paid : (max |x| |y|)^((s:ℕ)-1) ≤ 1 := by
    exact pow_le_one₀ (le_trans (abs_nonneg x) (le_max_left ..)) (max_le hx hy)
  calc
    _ ≤ ((s:ℝ) * |x-y|) * ‖source Z m q d φ v s‖ := mul_le_mul_of_nonneg_right
      (speed.trans (calc
        _ ≤ |x-y| * (s:ℝ) := mul_le_of_le_one_right (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _)) paid
        _ = _ := mul_comm _ _)) (norm_nonneg _)
    _ = _ := by ring

theorem finite_change (x t : ℝ) (hx : |x| ≤ 1) (ht : |t| ≤ 1) (hy : |forward Z m q x| ≤ 1) :
    ‖WilsonPositionFiniteMSBank.finite Z m d φ v q t - raw Z m q d φ v x‖ ≤
    slope Z m q d φ v * |t-forward Z m q x| + price Z m q d φ v * |x|^(q+1) := by
  let F := WilsonPositionFiniteMSBank.finite Z m d φ v q
  have tail : ‖F (forward Z m q x) - raw Z m q d φ v x‖ ≤ price Z m q d φ v * |x|^(q+1) := by
    rw [raw,price,Finset.sum_mul]
    change ‖(∑ s : Fin (q+1), (forward Z m q x : ℂ)^(s:ℕ) * source Z m q d φ v s) - _‖ ≤ _
    rw [← Finset.sum_sub_distrib]
    refine (norm_sum_le ..).trans (Finset.sum_le_sum ?_)
    intro s _
    rw [mul_comm ((forward Z m q x:ℂ)^(s:ℕ)),← mul_sub,norm_mul,← Complex.ofReal_pow,← Complex.ofReal_sub,
      Complex.norm_real,Real.norm_eq_abs,mul_assoc]
    exact mul_le_mul_of_nonneg_left (omitted Z m q s x hx) (norm_nonneg _)
  exact (norm_sub_le_norm_sub_add_norm_sub (F t) (F (forward Z m q x)) _).trans
    (add_le_add (lipschitz Z m q d φ v t (forward Z m q x) ht hy) tail)

end YM.Integration.WilsonPositionRawMesh
