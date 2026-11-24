import YM.Integration.WilsonTrueProjectedTransportedFare

/-! Transport of the exponential width for a single pinned marked input.
The finite expansion retains its terminal term at the actual cutoff. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPinnedWidthTransport
open Filter Finset Lattice Wilson RG
open scoped BigOperators

def elapsed (S : Schedule) (i j : ℕ) : ℝ := S.scale j - S.scale i

def transfer (S : Schedule) (b : ℕ → ℝ) (i j : ℕ) : ℝ :=
  b i * Real.exp (-elapsed S i j) / b j

def fraction (S : Schedule) (b : ℕ → ℝ) (j : ℕ) : ℝ :=
  b j / (((S.block j).val : ℝ)*b (j+1))

theorem self (S : Schedule) (b : ℕ → ℝ) {i : ℕ} (hb : 0 < b i) :
    transfer S b i i = 1 := by simp [transfer,elapsed,hb.ne']

theorem step (S : Schedule) (b : ℕ → ℝ) (i j : ℕ) (h : 0 < b j) (h' : 0 < b (j+1)) :
    transfer S b i (j+1) = transfer S b i j*fraction S b j := by
  have L : 0 < ((S.block j).val : ℝ) := by exact_mod_cast (S.block j).pos
  unfold transfer elapsed fraction
  rw [Schedule.scale_succ,show -(S.scale j + Real.log ((S.block j).val : ℝ)-S.scale i) =
    -(S.scale j-S.scale i)+(-Real.log ((S.block j).val : ℝ)) by ring,
    Real.exp_add,Real.exp_neg (Real.log ((S.block j).val:ℝ)),Real.exp_log L]
  field_simp [L.ne',h.ne',h'.ne']

theorem blocks (S : Schedule) (i n : ℕ) :
    (n:ℝ)*Real.log 3 ≤ elapsed S i (i+n) := by
  induction n with
  | zero => simp [elapsed]
  | succ n ih =>
    have low : (3:ℝ) ≤ (S.block (i+n)).val := by exact_mod_cast S.block_large (i+n)
    dsimp only [elapsed] at ih ⊢
    rw [show i+(n+1)=(i+n)+1 by omega,Schedule.scale_succ,Nat.cast_succ,add_mul,one_mul]
    linarith only [ih,Real.log_le_log (by norm_num) low]

theorem nonneg (S : Schedule) (b : ℕ → ℝ) {i j : ℕ}
    (hi : 0 ≤ b i) (hj : 0 ≤ b j) : 0 ≤ transfer S b i j :=
  div_nonneg (mul_nonneg hi (Real.exp_pos _).le) hj

/-- The interpolation exponents telescope in mesh time, including at the
last bare stencil. The norm of each marked input is taken at its own width. -/
theorem through (S : Schedule) (b value cost : ℕ → ℝ) (i n : ℕ)
    (width : ∀ j, i ≤ j → j ≤ i+n → 0 < b j)
    (one : ∀ j, i ≤ j → j < i+n →
      value j ≤ cost j+fraction S b j*value (j+1)) (terminal : value (i+n) ≤ cost (i+n)) :
    value i ≤ ∑ k ∈ range (n+1),transfer S b i (i+k)*cost (i+k) := by
  have run : ∀ m, m ≤ n → value i ≤
      (∑ k ∈ range m, transfer S b i (i+k)*cost (i+k)) + transfer S b i (i+m)*value (i+m) := by
    intro m
    induction m with
    | zero =>
      intro _
      simp [self S b (width i (le_refl _) (by omega))]
    | succ m ih =>
      intro hm
      have hj := width (i+m) (by omega) (by omega)
      have hn := width (i+m+1) (by omega) (by omega)
      have hτ := nonneg S b (width i (by omega) (by omega)).le hj.le
      have move := mul_le_mul_of_nonneg_left (one (i+m) (by omega) (by omega)) hτ
      have old := ih (show m≤n by omega)
      rw [sum_range_succ,show i+(m+1)=(i+m)+1 by omega,step S b i (i+m) hj hn]
      rw [mul_add,←mul_assoc] at move
      linarith only [old,move]
  have hτ := nonneg S b (width i (by omega) (by omega)).le (width (i+n) (by omega) (by omega)).le
  rw [sum_range_succ]
  exact (run n le_rfl).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left terminal hτ))

/-- A positive gross one-step inequality on the enrolled arrays gives the
logarithmic inequality without choosing an extremizing tensor or digit. -/
theorem log_step (S : Schedule) (b : ℕ → ℝ) (j : ℕ) {B A D : ℝ}
    (hB : 0 < B) (hA : 0 < A) (hD : 0 < D)
    (sale : B ≤ D*A^(fraction S b j)) :
    Real.log B ≤ Real.log D+fraction S b j*Real.log A := by
  have h := Real.log_le_log hB sale
  rwa [Real.log_mul hD.ne' (Real.rpow_pos_of_pos hA _).ne',Real.log_rpow hA] at h

private theorem geometric (r : ℝ) (hr : 0 ≤ r) (small : r < 1) (n : ℕ) :
    ∑ k ∈ range n,r^k ≤ (1-r)⁻¹ := by
  rw [inv_eq_one_div,le_div_iff₀ (sub_pos.mpr small)]
  have h := geom_sum_mul r n
  nlinarith only [h,pow_nonneg hr n]

private theorem quarter (t : ℝ) (ht : 0 ≤ t) :
    (1+t)^2 ≤ 16*Real.exp (t/2) := by
  have h : 1+t ≤ 4*Real.exp (t/4) := by linarith only [Real.add_one_le_exp (t/4)]
  have h2 := pow_le_pow_left₀ (by linarith : 0≤1+t) h 2
  calc
    _ ≤ _ := h2
    _ = _ := by rw [mul_pow,sq (Real.exp _),←Real.exp_add]; congr 2 <;> ring

/-- A bound independent of the top date and of the digit itinerary. On a
Wilson calendar z=1+log log beta the quadratic price is already subpower. -/
theorem quadratic (S : Schedule) (b value cost : ℕ → ℝ) (i n : ℕ) {z c E : ℝ}
    (hz : 0 ≤ z) (hc : 0 ≤ c) (hE : 0 ≤ E) (cap : b i ≤ 1)
    (width : ∀ j, i ≤ j → j ≤ i+n → 0 < b j)
    (aperture : ∀ j, i ≤ j → j ≤ i+n → (b j)⁻¹ ≤ z+c*elapsed S i j)
    (localFee : ∀ j, i ≤ j → j ≤ i+n → cost j ≤ E*(1+z+elapsed S i j))
    (one : ∀ j, i ≤ j → j < i+n →
      value j ≤ cost j+fraction S b j*value (j+1)) (terminal : value (i+n) ≤ cost (i+n)) :
    value i ≤ 16*(1+c)*E*(1+z)^2/(1-Real.exp (-(Real.log 3)/2)) := by
  let r := Real.exp (-(Real.log 3)/2)
  have small : r < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [Real.log_pos (by norm_num : (1:ℝ)<3)])
  let price := 16*(1+c)*E*(1+z)^2
  have pricePos : 0 ≤ price := by dsimp only [price]; positivity
  have each (k : ℕ) (hk : k ∈ range (n+1)) :
      transfer S b i (i+k)*cost (i+k) ≤ price*r^k := by
    have kj : i+k ≤ i+n := by have := mem_range.mp hk;omega
    have ij : i ≤ i+k := by omega
    let t := elapsed S i (i+k)
    have dt : (k:ℝ)*Real.log 3 ≤ t := blocks S i k
    have ht : 0 ≤ t := (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num))).trans dt
    have hb := width (i+k) ij kj
    have hi := width i le_rfl (by omega)
    have hτ := nonneg S b hi.le hb.le
    have hτ' : transfer S b i (i+k) ≤ (z+c*t)*Real.exp (-t) := by
      calc
        _ = b i*(b (i+k))⁻¹*Real.exp (-t) := by unfold transfer t; rw [div_eq_mul_inv]; ring
        _ ≤ 1*(z+c*t)*Real.exp (-t) :=
          mul_le_mul_of_nonneg_right (mul_le_mul cap (aperture _ ij kj) (inv_nonneg.mpr hb.le) zero_le_one) (Real.exp_pos _).le
        _ = _ := by ring
    have a : z+c*t ≤ (1+c)*(1+z)*(1+t) := by nlinarith only [hc,hz,ht,mul_nonneg hz hc,mul_nonneg hz ht,mul_nonneg (mul_nonneg hc hz) ht]
    have aa : 1+z+t ≤ (1+z)*(1+t) := by nlinarith only [mul_nonneg hz ht]
    have er : Real.exp (-t/2) ≤ r^k := by
      dsimp only [r]
      rw [←Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      nlinarith only [dt]
    have expEq : Real.exp (t/2)*Real.exp (-t)=Real.exp (-t/2) := by rw [←Real.exp_add]; congr 1; ring
    calc
      _ ≤ transfer S b i (i+k)*(E*(1+z+t)) := mul_le_mul_of_nonneg_left (localFee _ ij kj) hτ
      _ ≤ ((z+c*t)*Real.exp (-t))*(E*(1+z+t)) := mul_le_mul_of_nonneg_right hτ' (by positivity)
      _ ≤ ((1+c)*(1+z)*(1+t)*Real.exp (-t))*(E*((1+z)*(1+t))) :=
        mul_le_mul (mul_le_mul_of_nonneg_right a (Real.exp_pos _).le)
          (mul_le_mul_of_nonneg_left aa hE) (by positivity) (by positivity)
      _ = ((1+c)*E*(1+z)^2*Real.exp (-t))*(1+t)^2 := by ring
      _ ≤ ((1+c)*E*(1+z)^2*Real.exp (-t))*(16*Real.exp (t/2)) :=
        mul_le_mul_of_nonneg_left (quarter t ht) (by positivity)
      _ = price*Real.exp (-t/2) := by rw [←expEq]; dsimp only [price]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left er pricePos
  calc
    _ ≤ _ := through S b value cost i n width one terminal
    _ ≤ ∑ k ∈ range (n+1),price*r^k := sum_le_sum each
    _ = price*(∑ k ∈ range (n+1),r^k) := by rw [mul_sum]
    _ ≤ price*(1-r)⁻¹ := mul_le_mul_of_nonneg_left (geometric r (Real.exp_pos _).le small _) pricePos
    _ = _ := by rw [div_eq_mul_inv]

end YM.Integration.WilsonPinnedWidthTransport
