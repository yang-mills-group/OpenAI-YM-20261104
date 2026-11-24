import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Polynomial-in-the-height costs

At height `θ = log (1 / ε)`, allow a loss `(1+θ)^j`, even at *both* sides of
an estimate. `Bond` of §F compares two such functions. It prices not only each
function but also, separately and at the higher rate, their *difference*.
Keep the whole sample filter `l` (it need not be NeBot).
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.WiderProfiles
open Filter
open scoped Topology BigOperators

variable {I E : Type*} [NormedAddCommGroup E]
variable {R : Type*} [NormedRing R]
variable {l : Filter I} {θ : I → ℝ} {r s : ℝ}

/-- Rate `ε^r`, up to polynomial-in-log factors. -/
def Price (l : Filter I) (θ : I → ℝ) (r : ℝ) (x : I → E) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ a : ℕ, ∀ᶠ i in l,
    ‖x i‖ ≤ C * (1 + θ i)^a * Real.exp (-r * θ i)

abbrev Slow (l : Filter I) (θ : I → ℝ) (x : I → E) : Prop := Price l θ 0 x

structure Bond (l : Filter I) (θ : I → ℝ) (r : ℝ) (x y : I → E) : Prop where
  left_slow : Slow l θ x
  right_slow : Slow l θ y
  delta : Price l θ r (x-y)

namespace Price
variable {x y : I → E}

lemma tee (h : Price l θ r x) (he : x =ᶠ[l] y) : Price l θ r y := by
  obtain ⟨C, hC, a, ha⟩ := h
  refine ⟨C, hC, a, ?_⟩
  filter_upwards [ha, he] with i hi hi'
  rw [← hi']; exact hi

lemma zero (l : Filter I) (θ : I → ℝ) (r : ℝ) : Price l θ r (0 : I → E) :=
  ⟨1, zero_lt_one, 0, Eventually.of_forall fun i => by simp [(Real.exp_pos _).le]⟩

lemma bounded (C : ℝ) (hc : 0 < C) (h : ∀ᶠ i in l, ‖x i‖ ≤ C) : Price l θ 0 x :=
  ⟨C, hc, 0, by simpa using h⟩

lemma const (l : Filter I) (θ : I → ℝ) (a : E) : Price l θ 0 (fun _ => a) := by
  apply bounded (1 + ‖a‖) (by positivity)
  exact Eventually.of_forall (by simp)

lemma neg (h : Price l θ r x) : Price l θ r (-x) := by
  obtain ⟨C, hC, a, ha⟩ := h
  exact ⟨C, hC, a, by simpa using ha⟩

lemma mul {x y : I → R} (h : Price l θ r x) (hy : Price l θ s y) :
    Price l θ (r+s) (x*y) := by
  obtain ⟨C, hC, j, hj⟩ := h
  obtain ⟨D, hD, k, hk⟩ := hy
  refine ⟨C*D, mul_pos hC hD, j+k, ?_⟩
  filter_upwards [hj, hk] with i hi hi'
  rw [Pi.mul_apply]
  refine (norm_mul_le ..).trans ((mul_le_mul hi hi' (norm_nonneg _) ((norm_nonneg _).trans hi)).trans_eq ?_)
  rw [pow_add, show -(r+s) * θ i = -r * θ i + -s * θ i by ring, Real.exp_add]; ring

variable (nn : ∀ i, 0 ≤ θ i)
include nn

lemma add (h : Price l θ r x) (hy : Price l θ r y) : Price l θ r (x+y) := by
  obtain ⟨C, hC, j, hj⟩ := h
  obtain ⟨D, hD, k, hk⟩ := hy
  refine ⟨C+D, add_pos hC hD, j+k, ?_⟩
  filter_upwards [hj, hk] with i hi hi'
  rw [Pi.add_apply]
  have h1 : 1 ≤ 1 + θ i := le_add_of_nonneg_right (nn i)
  refine (norm_add_le ..).trans ((add_le_add hi hi').trans ?_)
  rw [add_mul, add_mul]
  apply add_le_add
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ h1 (Nat.le_add_right j k)) hC.le) (Real.exp_pos _).le
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ h1 (Nat.le_add_left k j)) hD.le) (Real.exp_pos _).le

lemma sub (h : Price l θ r x) (hy : Price l θ r y) : Price l θ r (x-y) :=
  sub_eq_add_neg x y ▸ add nn h hy.neg

lemma down (h : Price l θ r x) (hs : s ≤ r) : Price l θ s x := by
  obtain ⟨C, hC, j, hj⟩ := h
  refine ⟨C, hC, j, ?_⟩
  filter_upwards [hj] with i hi
  have h0 := nn i
  exact hi.trans (mul_le_mul_of_nonneg_left
    (Real.exp_monotone (mul_le_mul_of_nonneg_right (neg_le_neg hs) h0)) (by positivity))
end Price

namespace Bond
variable {x y z u : I → E}

lemma tee (h : Bond l θ r x y) (h1 : x =ᶠ[l] z) (h2 : y =ᶠ[l] u) : Bond l θ r z u :=
  ⟨h.left_slow.tee h1, h.right_slow.tee h2, h.delta.tee (h1.sub h2)⟩

lemma refl (x : I → E) (h : Price l θ 0 x) : Bond l θ r x x :=
  ⟨h, h, sub_self x ▸ Price.zero ..⟩

lemma const (l : Filter I) (θ : I → ℝ) (r : ℝ) (x : E) :
    Bond l θ r (fun _ => x) (fun _ => x) := refl _ (Price.const ..)

lemma neg (h : Bond l θ r x y) : Bond l θ r (-x) (-y) :=
  ⟨Price.neg h.left_slow, Price.neg h.right_slow, (show -x- -y=-(x-y) by abel) ▸ h.delta.neg⟩

variable (nn : ∀ i, 0 ≤ θ i)
include nn

lemma of_right (h : Price l θ r (x-y)) (hy : Price l θ 0 y) (hr : 0 ≤ r) : Bond l θ r x y :=
  ⟨sub_add_cancel x y ▸ Price.add nn (Price.down nn h hr) hy, hy, h⟩

lemma add (h : Bond l θ r x y) (h' : Bond l θ r z u) : Bond l θ r (x+z) (y+u) :=
  ⟨Price.add nn h.left_slow h'.left_slow, Price.add nn h.right_slow h'.right_slow,
   (show x+z-(y+u)=(x-y)+(z-u) by abel) ▸ Price.add nn h.delta h'.delta⟩

lemma sub (h : Bond l θ r x y) (h' : Bond l θ r z u) : Bond l θ r (x-z) (y-u) := by
  rw [sub_eq_add_neg, sub_eq_add_neg]; exact Bond.add nn h h'.neg

lemma mul {x y z u : I → R} (h : Bond l θ r x y) (h' : Bond l θ r z u) :
    Bond l θ r (fun i => x i * z i) (fun i => y i * u i) := by
  change Bond l θ r (x*z) (y*u)
  refine ⟨by simpa only [add_zero, Slow] using (Price.mul h.left_slow h'.left_slow),
    by simpa only [add_zero, Slow] using (Price.mul h.right_slow h'.right_slow), ?_⟩
  rw [show x*z-y*u = x*(z-u) + (x-y)*u by rw [mul_sub, sub_mul]; abel]
  exact Price.add nn (zero_add r ▸ Price.mul h.left_slow h'.delta)
    (add_zero r ▸ Price.mul h.delta h'.right_slow)

lemma sum {J : Type*} (F H : J → I → E) (s : Finset J)
    (h : ∀ j ∈ s, Bond l θ r (F j) (H j)) :
    Bond l θ r (fun i => ∑ j ∈ s, F j i) (fun i => ∑ j ∈ s, H j i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp_rw [Finset.sum_empty]; exact const l θ r 0
  | insert i s hi ih =>
    simp_rw [Finset.sum_insert hi]; exact Bond.add nn (h i (by simp)) (ih fun j hj => h j (by simp [hj]))

lemma prod {J K : Type*} [NormedCommRing K] (F H : J → I → K) (s : Finset J)
    (h : ∀ j ∈ s, Bond l θ r (F j) (H j)) :
    Bond l θ r (fun i => ∏ j ∈ s, F j i) (fun i => ∏ j ∈ s, H j i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp_rw [Finset.prod_empty]; exact const l θ r 1
  | insert i s hi ih =>
    simp_rw [Finset.prod_insert hi]; exact Bond.mul nn (h i (by simp)) (ih fun j hj => h j (by simp [hj]))
end Bond
end YM.FVA2.WiderProfiles
