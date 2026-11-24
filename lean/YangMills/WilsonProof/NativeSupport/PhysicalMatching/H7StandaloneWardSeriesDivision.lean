import YangMills.WilsonProof.NativeSupport.PhysicalMatching.H7StandaloneFiniteWardMatrix
import YM.MS.Book.Triang

noncomputable section
open scoped BigOperators
open Finset
namespace PhysicalMatching.H7StandaloneWardSeriesDivision
open H7StandaloneFiniteWardMatrix

def crop {X : Type*} [AddCommMonoid X] [Module ℂ X]
    (w : ℂ) (p : ℕ) (a : ℕ → X) : X :=
  ∑ k ∈ Iic p, w ^ k • a k

lemma act_smul_left (z : ℂ) (A : Matrix4) (u : Coords) :
    act (z • A) u = z • act A u := by
  ext i
  simp [act, Finset.mul_sum, mul_assoc]

lemma act_smul_right (z : ℂ) (A : Matrix4) (u : Coords) :
    act A (z • u) = z • act A u := by
  ext i
  simp [act, Finset.mul_sum, mul_left_comm, mul_assoc]

lemma act_sum_left {α : Type*} (t : Finset α) (A : α → Matrix4) (u : Coords) :
    act (∑ k ∈ t, A k) u = ∑ k ∈ t, act (A k) u := by
  classical
  ext i
  simp only [act, Matrix.sum_apply, Finset.sum_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

lemma act_sum_right {α : Type*} (t : Finset α) (A : Matrix4) (u : α → Coords) :
    act A (∑ k ∈ t, u k) = ∑ k ∈ t, act A (u k) := by
  classical
  ext i
  simp only [act, Finset.sum_apply, Finset.mul_sum]
  rw [Finset.sum_comm]

lemma size_smul (z : ℂ) (u : Coords) : size (z • u) = ‖z‖ * size u := by
  simp [size, Finset.mul_sum]

lemma size_sum {α : Type*} (t : Finset α) (u : α → Coords) :
    size (∑ k ∈ t, u k) ≤ ∑ k ∈ t, size (u k) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [size]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (size_add _ _).trans (add_le_add le_rfl ih)

theorem groundRow (B : Matrix4) (L : ℕ → Matrix4) (b : ℕ → Coords)
    (inverse : ∀ u, act (L 0) (act B u) = u) (n : ℕ) :
    (∑ q ∈ antidiagonal n, act (L q.1) (coefficients B L b q.2)) = b n := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => act (L i) (coefficients B L b j)) n]
  rw [Finset.sum_range_succ']
  simp only [Nat.zero_add, Nat.sub_zero]
  have balance := coefficientBalance B L b inverse n
  rw [add_comm]
  convert balance using 1
  rw [← Fin.sum_univ_eq_sum_range (fun k : ℕ =>
    act (L (k+1)) (coefficients B L b (n-(k+1)))) n]

theorem paidProduct (w : ℂ) (p : ℕ) (B : Matrix4) (L : ℕ → Matrix4)
    (b : ℕ → Coords) (inverse : ∀ u, act (L 0) (act B u) = u) :
    act (crop w p L) (crop w p (coefficients B L b)) =
      crop w p b + ∑ i ∈ Iic p, ∑ j ∈ Iic p,
        if p < i+j then w^(i+j) • act (L i) (coefficients B L b j) else 0 := by
  classical
  let u := coefficients B L b
  let K := fun i j : ℕ => if i+j ≤ p then w^(i+j) • act (L i) (u j) else 0
  have hK : ∀ i j, p < i+j → K i j = 0 := by
    intro i j hij
    simp [K, Nat.not_le_of_gt hij]
  have diagonal : ∀ n ∈ Iic p, (∑ q ∈ antidiagonal n, K q.1 q.2) = w^n • b n := by
    intro n hn
    have hn' : n ≤ p := mem_Iic.mp hn
    calc
      _ = ∑ q ∈ antidiagonal n, w^n • act (L q.1) (u q.2) := by
        apply Finset.sum_congr rfl
        intro q hq
        have hsum := Finset.mem_antidiagonal.mp hq
        simp [K, hsum, hn']
      _ = w^n • (∑ q ∈ antidiagonal n, act (L q.1) (u q.2)) := by
        rw [Finset.smul_sum]
      _ = w^n • b n := by rw [groundRow B L b inverse]
  have low : (∑ i ∈ Iic p, ∑ j ∈ Iic p, K i j) = crop w p b := by
    rw [YM.MS.Book.Program.price K p hK]
    exact Finset.sum_congr rfl diagonal
  change act (crop w p L) (crop w p u) = _
  calc
    _ = ∑ i ∈ Iic p, ∑ j ∈ Iic p, w^(i+j) • act (L i) (u j) := by
      simp only [crop, act_sum_left, act_sum_right, act_smul_left, act_smul_right,
        Finset.smul_sum, smul_smul, pow_add]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [mul_comm]
    _ = (∑ i ∈ Iic p, ∑ j ∈ Iic p, K i j) + ∑ i ∈ Iic p, ∑ j ∈ Iic p,
          if p < i+j then w^(i+j) • act (L i) (u j) else 0 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      by_cases h : i+j ≤ p <;> simp [K, h]
    _ = _ := by rw [low]

theorem cropSize (w : ℂ) (p : ℕ) (a : ℕ → Coords) (hw : ‖w‖ ≤ 1) :
    size (crop w p a) ≤ ∑ k ∈ Iic p, size (a k) := by
  apply (size_sum _ _).trans
  apply Finset.sum_le_sum
  intro k hk
  rw [size_smul, norm_pow]
  exact mul_le_of_le_one_left (size_nonneg _) (pow_le_one₀ (norm_nonneg w) hw)

theorem tailPrice (w : ℂ) (p : ℕ) (L : ℕ → Matrix4) (u : ℕ → Coords)
    (hw : ‖w‖ ≤ 1) :
    size (∑ i ∈ Iic p, ∑ j ∈ Iic p,
      if p < i+j then w^(i+j) • act (L i) (u j) else 0) ≤
        (∑ i ∈ Iic p, ∑ j ∈ Iic p, size (act (L i) (u j))) * ‖w‖^(p+1) := by
  apply (size_sum _ _).trans
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  apply (size_sum _ _).trans
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j hj
  by_cases h : p < i+j
  · rw [if_pos h, size_smul, norm_pow, mul_comm]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one (norm_nonneg w) hw (by omega)) (size_nonneg _)
  · rw [if_neg h, show size (0 : Coords) = 0 from by simp [size]]
    exact mul_nonneg (size_nonneg _) (pow_nonneg (norm_nonneg _) _)

theorem original (w : ℂ) (p : ℕ) (A B : Matrix4) (L : ℕ → Matrix4)
    (b : ℕ → Coords) (physical rhs : Coords) (C D E : ℝ)
    (leftInverse : ∀ u, act B (act (L 0) u) = u)
    (rightInverse : ∀ u, act (L 0) (act B u) = u)
    (small : matrixSize B * matrixSize (L 0 - A) ≤ 1/2)
    (heat : ‖w‖ ≤ 1)
    (entries : matrixSize (A - crop w p L) ≤ C * ‖w‖^(p+1))
    (rightSide : size (rhs - crop w p b) ≤ D * ‖w‖^(p+1))
    (physicalRows : size (act A physical - rhs) ≤ E * ‖w‖^(p+1)) :
    size (physical - crop w p (coefficients B L b)) ≤
      2 * matrixSize B * (E + D + C*(∑ k ∈ Iic p, size (coefficients B L b k)) +
        ∑ i ∈ Iic p, ∑ j ∈ Iic p, size (act (L i) (coefficients B L b j))) * ‖w‖^(p+1) := by
  let u := coefficients B L b
  let z := crop w p u
  let t := ‖w‖^(p+1)
  let high := ∑ i ∈ Iic p, ∑ j ∈ Iic p,
    if p < i+j then w^(i+j) • act (L i) (u j) else 0
  have hprod : act (crop w p L) z = crop w p b + high :=
    paidProduct w p B L b rightInverse
  have hsplit : rhs - act A z = (rhs - crop w p b) +
      (-act (A-crop w p L) z + -high) := by
    rw [subAct, hprod]
    abel
  have negSize (v : Coords) : size (-v) = size v := by simp [size]
  have hterm : size (act (A-crop w p L) z) ≤
      C*t*(∑ k ∈ Iic p, size (u k)) :=
    (actPrice _ _).trans (mul_le_mul entries (cropSize w p u heat)
      (size_nonneg _) ((matrixSize_nonneg _).trans entries))
  have residual := size_add (-act (A-crop w p L) z) (-high)
  rw [negSize, negSize] at residual
  have hres := size_add (rhs-crop w p b) (-act (A-crop w p L) z + -high)
  rw [←hsplit] at hres
  have ht : size high ≤ (∑ i ∈ Iic p, ∑ j ∈ Iic p, size (act (L i) (u j))) * t :=
    tailPrice w p L u heat
  have trueRows : size (act A physical-rhs) + size (rhs-act A z) ≤
    (E+D+C*(∑ k ∈ Iic p, size (u k)) +
      ∑ i ∈ Iic p, ∑ j ∈ Iic p, size (act (L i) (u j)))*t := by
    change size (act A physical-rhs) ≤ E*t at physicalRows
    change size (rhs-crop w p b) ≤ D*t at rightSide
    linarith only [physicalRows,rightSide,hterm,ht,residual,hres]
  apply (fitted B (L 0) A leftInverse small physical z rhs).trans
  calc
    _ ≤ 2*matrixSize B * ((E+D+C*(∑ k ∈ Iic p, size (u k)) +
          ∑ i ∈ Iic p, ∑ j ∈ Iic p, size (act (L i) (u j)))*t) :=
      mul_le_mul_of_nonneg_left trueRows (mul_nonneg (by norm_num) (matrixSize_nonneg _))
    _ = _ := by dsimp only [u,t]; ring

end PhysicalMatching.H7StandaloneWardSeriesDivision

