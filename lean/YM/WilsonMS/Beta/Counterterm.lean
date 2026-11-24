import YM.WilsonMS.Columns.PaidLate
/-!
# Which high-mode terms measure the (η dependence of) the Coupling

A perturbative-order-two AA rank-two tensor, the ghost source derivative
at that order, and a cubic-order token in the full log-interaction
measure the three changes. Equating *just* cutoff terms directly would
be wrong: loop shifts will contribute to each. Compare whole kernels,
and read the *change* when varying MS η with fixed R. This file pulls
those jets out from the PRE-integration interaction.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.BetaValue
open Function Filter Set Finset MeasureTheory Metric
open LoopRank Lattice MS
open Plane Koszul Heat Flux Landau Tone Momentum Real Frame Wire Color Detect Native Native.Wilsonian
  Paint
open Book Convolve City Logarithm Program Signal
open Cylinder Lab Menus
open PowerSeries (coeff)
open scoped Topology ContDiff BigOperators

variable {G : Gauge} {P : Team} (hp : Valid P) (x y : ℝ)

private lemma post_car (p : Team) (φ : Dot G Cover) (k : ℕ) (z : Legs (Lane4 G)) :
    run (train (Y p x) k φ) z = coeff k (z.map (fun u => adap p u.1.1 x)).prod * run φ z := by
  unfold run train
  let W := (fieldV p x ∘ (Prod.fst : Lane4 G → Branch G Axis))
  let V := (fieldV p x ∘ (Prod.fst : LightMode G Cover → _))
  have ht (i : Lane4 G) (j : LightMode G Cover) (h : paywave i j ≠ 0) : V j = W i :=
    Eq.symm (congr_arg (fieldV p x) (in_light i j h))
  rw [← pennantC (coeff k) φ V W paywave ht]
  rfl

variable (V : T (Dot G Cover))
local notation "Σ" => Program.shift P x
local notation "Q" => substitute (Program.shift P x) V

private lemma transports (k : ℕ) (z : Legs (Lane4 G)) :
    run (wobble G P x V k) z =
      ∑ i ∈ antidiagonal k, coeff i.1 (z.map (fun u => adap P u.1.1 x)).prod * run (Q i.2) z := by
  rw [wobble, LinearMap.comp_apply, rolls, map_sum, Finset.sum_apply]
  exact Finset.sum_congr rfl (fun _ _ => post_car x ..)

private lemma zero_term (w : List (Lane4 G)) : coeff 0 (w.map (fun u => adap P u.1.1 x)).prod = 1 := by
  induction w with
  | nil => simp
  | cons i l ih =>
    simp_rw [List.map_cons, List.prod_cons, PowerSeries.coeff_mul, Finset.Nat.antidiagonal_zero,
      Finset.sum_singleton, ih, mul_one]
    exact adap0 P x _

include hp

private lemma odd_term (w : List (Lane4 G)) :
    coeff 1 (w.map (fun u => adap P u.1.1 x)).prod = 0 ∧
      coeff 3 (w.map (fun u => adap P u.1.1 x)).prod = 0 := by
  suffices H : rulesPS (w.map (fun u => adap P u.1.1 x)).prod 0 by
    exact ⟨H 1 (fun ⟨i, hi⟩ => by omega), H 3 (fun ⟨i, hi⟩ => by omega)⟩
  induction w with
  | nil => exact rulesPS.one
  | cons i w ih => exact (Z_even x hp _).pair ih

omit hp in
private lemma ranger (n : ℕ) : Finset.Iic n = Finset.range (n + 1) := by
  ext
  simp

omit hp in
private lemma push_one : Q 1 = V 1 := by
  rw [rules, ranger, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [Program.cut, pow_zero, pow_one, ann, one_smul, zero_add]
  simp

private lemma push_two : Q 2 = V 2 := by
  rw [rules, ranger]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [root_first (share ..) (ann ..),
    show Program.cut Σ 1 2 = coeff 2 Σ from (by rw [Program.cut, pow_one]),
    φ_odd x hp 2 (fun ⟨i, hi⟩ => by omega)]
  simp [Program.cut]

private lemma push_three : Q 3 = V 3 + coeff 3 Σ • V 1 := by
  rw [rules, ranger]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [root_first (share ..) (ann ..), show Program.cut Σ 1 3 = coeff 3 Σ from (by simp [Program.cut]),
    show Program.cut Σ 2 3 = 0 from (φ_odd x hp |>.plow 2) 3 (fun ⟨i, hi⟩ => by omega)]
  simp only [Program.cut, pow_zero, PowerSeries.coeff_one, if_neg (show (3 : ℕ) ≠ 0 from by decide),
    one_smul, zero_smul, add_zero, zero_add, add_comm (_ • V 1)]

omit hp in
private lemma anti_diag₀ {I : Type} [AddCommMonoid I] (k : ℕ) (p : ℕ × ℕ → I) :
    (∑ i ∈ antidiagonal k, p i) = ∑ x ∈ Finset.range (k + 1), p (x, k - x) :=
  Finset.Nat.sum_antidiagonal_eq_sum_range_succ (f := fun i j => p (i, j)) _

lemma point₁ (z : Legs (Lane4 G)) : run (wobble G P x V 1) z = run (V 1) z := by
  rw [transports, anti_diag₀]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [zero_term x, odd_term hp x _ |>.1, one_mul, zero_mul, add_zero, zero_add, Nat.sub_zero,
    push_one x]

lemma point₂ (z : Legs (Lane4 G)) :
    run (wobble G P x V 2) z =
      run (V 2) z + coeff 2 ((z.map (fun u => adap P u.1.1 x)).prod) * run (V 0) z := by
  rw [transports, anti_diag₀]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [zero_term x, odd_term hp x _ |>.1, one_mul, zero_mul, add_zero, push_two hp x, zero_add,
    Nat.sub_self, Program.pay0]

lemma point₃ (z : Legs (Lane4 G)) :
    run (wobble G P x V 3) z =
      run (V 3) z +
        (coeff 3 (Program.shift P x) + coeff 2 ((z.map (fun u => adap P u.1.1 x)).prod)) *
          run (V 1) z := by
  rw [transports, anti_diag₀]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [zero_term x, odd_term hp x _ |>.1, odd_term hp x _ |>.2, one_mul, zero_mul, zero_mul, zero_add,
    add_zero, add_zero, show 3 - 2 = (1 : ℕ) from rfl, show 3 - 0 = (3 : ℕ) from rfl, push_one x,
    push_three hp x, map_add, map_smul]
  simp_rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, add_assoc]

end YM.WilsonMS.BetaValue
