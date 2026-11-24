import YM.Integration.WilsonWalkMatrixSecant
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Algebra.BigOperators.Ring.List

/-! Ordered expansion of a genuine lattice word through any contact order.
The first omitted contact retains the original sampled unitary suffix. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonWalkTruncation
open Lattice Wilson WilsonWalkMatrixSecant
open scoped Classical BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {c : Side}

def increment (U Q : Config G c) (x : Site c) (d : Step) : G.Mat :=
  G.mat (d.read U x) - G.mat (d.read Q x)

theorem increment_norm (g Q : Config G c) (x : Site c) (d : Step) :
    ‖increment (g*Q) Q x d‖ = ‖G.mat (g (d.used x))-1‖ := by
  let e := d.used x
  have h : G.mat (g e * Q e) - G.mat (Q e) = (G.mat (g e)-1)*G.mat (Q e) := by
    rw [G.mat_mul,sub_mul,one_mul]
  have hnorm : ‖G.mat (g e * Q e) - G.mat (Q e)‖ = ‖G.mat (g e)-1‖ := by
    rw [h,Gauge.frob_mul_eq _ _ (G.mat_mul_star _)]
  by_cases hd : d.neg = true
  · simpa only [increment,Step.read,if_pos hd,Pi.mul_apply,G.mat_inv,←star_sub,norm_star,e] using hnorm
  · simpa only [increment,Step.read,if_neg hd,Pi.mul_apply,e] using hnorm

/-- Choose ordered occurrences through degree n. Each unchanged letter comes
from the predicted configuration, and each contact is the sampled oriented
letter minus this very prediction. -/
def jet (U Q : Config G c) : Site c → Walk → ℕ → G.Mat
  | _, [], _ => 1
  | x, d::w, 0 => G.mat (d.read Q x) * jet U Q (x+d.vec) w 0
  | x, d::w, n+1 => G.mat (d.read Q x) * jet U Q (x+d.vec) w (n+1) +
      increment U Q x d * jet U Q (x+d.vec) w n

def layer (U Q : Config G c) (x : Site c) (w : Walk) : ℕ → G.Mat
  | 0 => jet U Q x w 0
  | n+1 => jet U Q x w (n+1) - jet U Q x w n

theorem layer_zero (U Q : Config G c) (x : Site c) (w : Walk) :
    layer U Q x w 0 = G.mat (travel Q x w) := by
  induction w generalizing x with
  | nil => simp [layer,jet,travel]
  | cons d w ih =>
    change G.mat (d.read Q x)*layer U Q (x+d.vec) w 0 = G.mat (d.read Q x * travel Q (x+d.vec) w)
    rw [ih,G.mat_mul]

theorem layer_cons (U Q : Config G c) (x : Site c) (d : Step) (w : Walk) (n : ℕ) :
    layer U Q x (d::w) (n+1) =
      G.mat (d.read Q x) * layer U Q (x+d.vec) w (n+1) +
      increment U Q x d * layer U Q (x+d.vec) w n := by
  cases n <;> simp only [layer,jet,mul_sub] <;> abel

theorem jet_eq_sum (U Q : Config G c) (x : Site c) (w : Walk) (n : ℕ) :
    jet U Q x w n = ∑ k ∈ Finset.range (n+1), layer U Q x w k := by
  induction n with
  | zero => simp [layer]
  | succ n ih =>
    rw [Finset.sum_range_succ,←ih,layer]
    abel

def remainder (U Q : Config G c) (x : Site c) (w : Walk) (n : ℕ) : G.Mat :=
  G.mat (travel U x w) - jet U Q x w n

/-- On the first unretained contact, the suffix is the original sampled
transport on every remaining oriented edge. -/
theorem stopping (U Q : Config G c) (x : Site c) (d : Step) (w : Walk) :
    remainder U Q x (d::w) 0 =
      G.mat (d.read Q x) * remainder U Q (x+d.vec) w 0 +
      increment U Q x d * G.mat (travel U (x+d.vec) w) := by
  simp only [remainder,jet,travel,G.mat_mul,increment,mul_sub,sub_mul]
  abel

theorem continuing (U Q : Config G c) (x : Site c) (d : Step) (w : Walk) (n : ℕ) :
    remainder U Q x (d::w) (n+1) =
      G.mat (d.read Q x)*remainder U Q (x+d.vec) w (n+1) +
      increment U Q x d*remainder U Q (x+d.vec) w n := by
  simp only [remainder,jet,travel,G.mat_mul,increment,mul_sub,sub_mul]
  abel

/-- Sum of products over ordered sublists, retaining the original multiplicity
of any link traversed more than once. -/
def debit {α : Type*} (r : α → ℝ) (l : List α) (k : ℕ) : ℝ :=
  ((List.sublistsLen k l).map (fun s => (s.map r).prod)).sum

@[simp] theorem debit_zero {α : Type*} (r : α → ℝ) (l : List α) : debit r l 0 = 1 := by
  simp [debit]

@[simp] theorem debit_cons {α : Type*} (r : α → ℝ) (e : α) (l : List α) (k : ℕ) :
    debit r (e::l) (k+1) = debit r l (k+1) + r e * debit r l k := by
  simp only [debit,List.sublistsLen_succ_cons,List.map_append,List.sum_append,List.map_map,
    Function.comp_def,List.map_cons,List.prod_cons,List.sum_map_mul_left]

theorem count (x : Site c) (w : Walk) (k : ℕ) :
    (List.sublistsLen k (occurrences x w)).length = w.length.choose k ∧
    (List.sublistsLen k (occurrences x w)).length ≤ w.length^k := by
  rw [List.length_sublistsLen,length_occurrences]
  exact ⟨rfl,Nat.choose_le_pow _ _⟩

/-- Every first omitted contact is charged by its actual link displacement.
The original unmarked prefix and sampled suffix act isometrically. -/
theorem bound (g Q : Config G c) (x : Site c) (w : Walk) (n : ℕ) :
    ‖remainder (g*Q) Q x w n‖ ≤
      debit (fun e => ‖G.mat (g e)-1‖) (occurrences x w) (n+1) := by
  induction w generalizing x n with
  | nil => simp [remainder,jet,travel,occurrences,debit]
  | cons d w ih =>
    cases n with
    | zero =>
      rw [stopping,occurrences,debit_cons,debit_zero,mul_one]
      refine (norm_add_le ..).trans ?_
      rw [Gauge.mul_frob_eq _ _ (G.mat_star_mul _),Gauge.frob_mul_eq _ _ (G.mat_mul_star _),increment_norm]
      exact add_le_add (ih (x+d.vec) 0) (le_refl ‖G.mat (g (d.used x))-1‖)
    | succ n =>
      rw [continuing,occurrences,debit_cons]
      refine (norm_add_le ..).trans (add_le_add ?_ ?_)
      · rw [Gauge.mul_frob_eq _ _ (G.mat_star_mul _)]
        exact ih (x+d.vec) (n+1)
      · apply (norm_mul_le ..).trans
        rw [increment_norm]
        exact mul_le_mul_of_nonneg_left (ih (x+d.vec) n) (norm_nonneg _)

theorem exact_of_length_le (g Q : Config G c) (x : Site c) (w : Walk) (n : ℕ) (h : w.length ≤ n) :
    jet (g*Q) Q x w n = G.mat (travel (g*Q) x w) := by
  have hh : (occurrences x w).length < n+1 := by rw [length_occurrences]; omega
  have hz := bound g Q x w n
  rw [debit,List.sublistsLen_of_length_lt hh,List.map_nil,List.sum_nil,
    norm_le_zero_iff,remainder,sub_eq_zero] at hz
  exact hz.symm

end YM.Integration.WilsonWalkTruncation
end
