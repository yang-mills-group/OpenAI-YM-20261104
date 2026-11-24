import YM.Integration.ActualNormalizedMarked
import YM.Next.RANK.Exponential

/-! Nonlinear error conversion for the actual normalized marked polynomial.
The coefficient supremum over independent tests and conditioning fields is taken
before the weighted sum. A supplied coefficient majorant of a connected residual
is converted to an error bound for removing that residual from the actual marked
polynomial. This does not supply the physical connected residual or its small
local majorant; those remain separate supplier obligations. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.UniformPolynomialComparison
open Marker Finset
open scoped BigOperators Classical

variable {ι α : Type*} [DecidableEq ι] {J : Census ι}

def Positive (A : Poly J) : Prop :=
  ∀ q, 0 ≤ (A.part q).re ∧ (A.part q).im = 0

def Dominates (A : Poly J) (F : α → Poly J) : Prop :=
  ∀ x q, ‖(F x).part q‖ ≤ (A.part q).re

lemma Positive.norm {A : Poly J} (hA : Positive A) (q : J.Mode) :
    ‖A.part q‖ = (A.part q).re := by
  have h : A.part q = ((A.part q).re : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa using (hA q).2
  rw [h, Complex.norm_real, Real.norm_of_nonneg (hA q).1]
  rfl

lemma positive_one : Positive (1 : Poly J) := by
  intro q
  simp only [Poly.one_part]
  split <;> norm_num

lemma positive_zero : Positive (0 : Poly J) := by
  intro q
  norm_num [Poly.part_nil]

lemma Positive.add {A B : Poly J} (hA : Positive A) (hB : Positive B) :
    Positive (A+B) := by
  intro q
  simp only [Poly.part_plus, Complex.add_re, Complex.add_im]
  exact ⟨add_nonneg (hA q).1 (hB q).1, by rw [(hA q).2, (hB q).2]; norm_num⟩

lemma Positive.mul {A B : Poly J} (hA : Positive A) (hB : Positive B) :
    Positive (A*B) := by
  intro q
  rw [Poly.part_mul]
  simp only [Complex.re_sum, Complex.im_sum]
  constructor
  · apply sum_nonneg
    intro a _
    apply sum_nonneg
    intro b _
    split_ifs
    · simp only [Complex.mul_re, (hA a).2, (hB b).2, zero_mul, sub_zero]
      exact mul_nonneg (hA a).1 (hB b).1
    · norm_num
  · apply sum_eq_zero
    intro a _
    apply sum_eq_zero
    intro b _
    split_ifs <;> simp [(hA a).2, (hB b).2]

lemma Positive.pow {A : Poly J} (hA : Positive A) (n : ℕ) : Positive (A^n) := by
  induction n with
  | zero => simpa using positive_one (J := J)
  | succ n ih => simpa only [pow_succ] using ih.mul hA

lemma dominates_one : Dominates (1 : Poly J) (fun _ : α => 1) := by
  intro x q
  rw [positive_one.norm]

lemma Dominates.neg {A : Poly J} {F : α → Poly J} (hF : Dominates A F) :
    Dominates A (fun x => -F x) := by
  intro x q
  simpa only [show (-F x).part q = -(F x).part q from rfl, norm_neg] using hF x q

lemma Dominates.mul {A B : Poly J} {F G : α → Poly J}
    (hF : Dominates A F) (hG : Dominates B G) (hA : Positive A) (hB : Positive B) :
    Dominates (A*B) (fun x => F x*G x) := by
  intro x q
  rw [Poly.part_mul, Poly.part_mul]
  simp only [Complex.re_sum]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro a _
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro b _
  split_ifs
  · rw [norm_mul, Complex.mul_re, (hA a).2, (hB b).2, zero_mul, sub_zero]
    exact mul_le_mul (hF x a) (hG x b) (norm_nonneg _) (hA a).1
  · norm_num

lemma Dominates.pow {A : Poly J} {F : α → Poly J}
    (hF : Dominates A F) (hA : Positive A) (n : ℕ) :
    Dominates (A^n) (fun x => (F x)^n) := by
  induction n with
  | zero => simpa using dominates_one (α := α) (J := J)
  | succ n ih => simpa only [pow_succ] using ih.mul hF (hA.pow n) hA

variable [Fintype ι]

/-- The finite exponential with its constant term removed. -/
def tail (A : Poly J) : Poly J :=
  ∑ n ∈ range (Fintype.card ι), ((n+1).factorial : ℂ)⁻¹ • A^(n+1)

lemma pass_eq_one_add_tail (A : Poly J) : Poly.pass A = 1+tail A := by
  unfold Poly.pass tail
  rw [sum_range_succ']
  simp [add_comm]

lemma Positive.tail {A : Poly J} (hA : Positive A) : Positive (tail A) := by
  intro q
  unfold UniformPolynomialComparison.tail
  rw [Poly.part_sum]
  simp only [Poly.part_smul, Complex.re_sum, Complex.im_sum]
  constructor
  · apply sum_nonneg
    intro n _
    have hp := hA.pow (n+1) q
    have hp0 := hp.1
    simp only [Complex.mul_re]
    norm_num
    positivity
  · apply sum_eq_zero
    intro n _
    have hp := hA.pow (n+1) q
    simp [hp.2]

lemma Dominates.tail {A : Poly J} {F : α → Poly J}
    (hF : Dominates A F) (hA : Positive A) :
    Dominates (tail A) (fun x => tail (F x)) := by
  intro x q
  unfold UniformPolynomialComparison.tail
  rw [Poly.part_sum, Poly.part_sum]
  simp only [Poly.part_smul, Complex.re_sum]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro n _
  rw [norm_mul]
  have hp := hA.pow (n+1) q
  have hb := hF.pow hA (n+1) x q
  simp only [Complex.mul_re]
  norm_num
  exact mul_le_mul_of_nonneg_left hb (by positivity)

/-- Sum of coefficient suprema, not the supremum of a pre-summed norm. -/
def uniformPrice (w : ι → ℝ) (F : α → Poly J) : ℝ :=
  ∑ q : J.Mode, Poly.toll w q * envelope (fun x => ‖(F x).part q‖)

omit [Fintype ι] in
lemma uniformPrice_le {A : Poly J} {F : α → Poly J}
    (hA : Positive A) (hF : Dominates A F) {w : ι → ℝ} (hw : ∀ i, 0 < w i) :
    uniformPrice w F ≤ Poly.price w A := by
  unfold uniformPrice Poly.price
  apply sum_le_sum
  intro q _
  rw [hA.norm]
  exact mul_le_mul_of_nonneg_left (envelope_le (hA q).1 (fun x => hF x q))
    (Poly.worth hw q).le

omit [Fintype ι] in
lemma positive_price_add {A B : Poly J} (hA : Positive A) (hB : Positive B)
    (w : ι → ℝ) : Poly.price w (A+B) = Poly.price w A + Poly.price w B := by
  unfold Poly.price
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro q _
  rw [(hA.add hB).norm, hA.norm, hB.norm, Poly.part_plus, Complex.add_re, mul_add]

lemma tail_price_le {A : Poly J} (hA : Positive A) {w : ι → ℝ}
    (hw : ∀ i, 0 < w i) :
    Poly.price w (tail A) ≤ Real.exp (Poly.price w A)-1 := by
  have h := Poly.pass_budget hw A
  rw [pass_eq_one_add_tail, positive_price_add positive_one hA.tail, Poly.one_price] at h
  linarith

/-- A coefficientwise bound on a connected polynomial yields an exponential
bound on its full marked response, with the supremum still inside every coefficient. -/
theorem exponential_error_bound {B : Poly J} {D : α → Poly J}
    (hB : Positive B) (hD : Dominates B D)
    {w : ι → ℝ} (hw : ∀ i, 0 < w i) :
    uniformPrice w (fun x => Poly.pass (D x) - 1) ≤
      Real.exp (Poly.price w B) - 1 := by
  have hd : Dominates (tail B) (fun x => Poly.pass (D x) - 1) := by
    intro x q
    change ‖(Poly.pass (D x) - 1).part q‖ ≤ _
    rw [pass_eq_one_add_tail, add_sub_cancel_left]
    exact hD.tail hB x q
  exact (uniformPrice_le hB.tail hd hw).trans (tail_price_le hB hw)

/-- Removing a connected residual from a normalized polynomial. -/
def error (F D : α → Poly J) (x : α) : Poly J :=
  F x - F x * Poly.pass (-D x)

lemma error_eq (F D : α → Poly J) (x : α) :
    error F D x = -(F x * tail (-D x)) := by
  unfold error
  rw [pass_eq_one_add_tail]
  ring

/-- A nonlinear comparison whose majorants stay coefficientwise uniform over
all test and field choices. No norm-equivalence or test-space dimension enters. -/
theorem removal_bound {A B : Poly J} {F D : α → Poly J}
    (hA : Positive A) (hB : Positive B)
    (hF : Dominates A F) (hD : Dominates B D)
    {w : ι → ℝ} (hw : ∀ i, 0 < w i) :
    uniformPrice w (error F D) ≤
      Poly.price w A * (Real.exp (Poly.price w B)-1) := by
  have hE : Dominates (A*tail B) (error F D) := by
    have h := (hF.mul (hD.neg.tail hB) hA hB.tail).neg
    intro x q
    rw [error_eq]
    exact h x q
  apply (uniformPrice_le (hA.mul hB.tail) hE hw).trans
  apply (Poly.multiplication hw A (tail B)).trans
  exact mul_le_mul_of_nonneg_left (tail_price_le hB hw) (Poly.nonnegative hw A)

end YM.Integration.UniformPolynomialComparison

namespace YM.Integration
open Marker Finset Lattice Wilson RG
open RemainderComparison.Typeface
open UniformPolynomialComparison
open scoped BigOperators Classical

variable {G : Gauge} {ι : Type} [Fintype ι] [DecidableEq ι]
    {E : ι → Type*} (J : Census ι)
    (C : Family G) {N p m : ℕ} (hC : C.Makes) (hm : m < N)
    (M : ∀ i, Portrait (C.path.rep N p (m+1)) (E i))

def portraitMajorant : Poly J :=
  Poly.inject fun q => ((∏ i ∈ q.val, (M i).weight : ℝ) : ℂ)

omit [Fintype ι] in
lemma portraitMajorant_positive (base : ∀ i, E i) :
    Positive (portraitMajorant J C M) := by
  intro q
  constructor
  · exact (norm_nonneg _).trans (portraitInput_part_bound M J base 1 q)
  · rfl

include hC hm
omit [Fintype ι] in
lemma normalizedPortrait_dominated :
    Dominates (portraitMajorant J C M)
      (fun x : (∀ i, E i) × Config G (C.side m p) =>
        normalizedPortrait J C M x.1 x.2) := by
  intro x q
  exact normalizedPortrait_bound J C hC hm M x.1 x.2 q
omit hC hm

omit [Fintype ι] in
lemma portraitMajorant_price (base : ∀ i, E i) (w : ι → ℝ) :
    Poly.price w (portraitMajorant J C M) =
      ∑ q : J.Mode, Poly.toll w q * ∏ i ∈ q.val, (M i).weight := by
  unfold Poly.price
  apply sum_congr rfl
  intro q _
  rw [(portraitMajorant_positive J C M base).norm]
  rfl

include hC hm

/-- The literal actual normalized marked polynomial loses at most this amount
when its supplied connected residual is removed. The conclusion takes the
independent-test and conditioning-field supremum separately in every coefficient
before summing its weight. It does not assert that the residual bound has been
proved by the physical local-comparison suppliers. -/
theorem actual_normalized_residual_removal (base : ∀ i, E i)
    (D : ((∀ i, E i) × Config G (C.side m p)) → Poly J)
    (b : J.Mode → ℝ) (hb : ∀ q, 0 ≤ b q)
    (hD : ∀ x q, ‖(D x).part q‖ ≤ b q)
    (hquiet : ∀ x, (D x).part J.quiet = 0)
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) :
    uniformPrice w (error
      (fun x : (∀ i, E i) × Config G (C.side m p) =>
        normalizedPortrait J C M x.1 x.2) D) ≤
        (∑ q : J.Mode, Poly.toll w q * ∏ i ∈ q.val, (M i).weight) *
          (Real.exp (∑ q : J.Mode, Poly.toll w q * b q)-1) ∧
    (∀ x : (∀ i, E i) × Config G (C.side m p),
      (normalizedPortrait J C M x.1 x.2 * Poly.pass (-D x)).part J.quiet = 1) := by
  let B : Poly J := Poly.inject fun q => (b q : ℂ)
  have hB : Positive B := fun q => ⟨hb q, rfl⟩
  have hd : Dominates B D := hD
  have hprice : Poly.price w B = ∑ q : J.Mode, Poly.toll w q * b q := by
    unfold Poly.price
    apply sum_congr rfl
    intro q _
    rw [hB.norm]
    rfl
  constructor
  · have h := removal_bound (portraitMajorant_positive J C M base) hB
      (normalizedPortrait_dominated J C hC hm M) hd hw
    rw [portraitMajorant_price J C M base w, hprice] at h
    exact h
  · intro x
    have hz : (-D x).part J.quiet = 0 := by
      change -(D x).part J.quiet = 0
      rw [hquiet x, neg_zero]
    rw [Poly.quiet_mul, normalizedPortrait_quiet J C hC hm M,
      Poly.pass_part _ hz, one_mul]

end YM.Integration
