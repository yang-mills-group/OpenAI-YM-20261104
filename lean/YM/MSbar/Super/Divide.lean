import Mathlib.Data.List.Permutation
import Mathlib.Analysis.Complex.Basic

/-!
# Koszul-signed shuffles for perturbative vertices

All density Taylor slots are symmetric (when parity is true, antisymmetric in such slots).
Polarized coefficients use derivatives, i.e. there is an implicit `1/rank!` on reconstructing
the actual polynomial from its `rank` coefficients with sums over ordered indices. Shuffles in
products of any two vertices therefore have no other factorials.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Super
open Function
open scoped BigOperators
variable {α : Type*}

/-- The basic Koszul sign character. -/
def twist (a b : Bool) : ℂ := if a && b then -1 else 1
lemma twist_comm (a b : Bool) : twist a b=twist b a := by unfold twist; rw [Bool.and_comm]
@[simp] lemma twist_false (a : Bool) : twist false a=1 := by cases a <;> rfl
@[simp] lemma twist_false' (a : Bool) : twist a false=1 := by rw [twist_comm]; simp
@[simp] lemma twist_true : twist true true = -1 := rfl
@[simp] lemma twist_mm (a b : Bool) : twist a b * twist a b =1 := by cases a <;> cases b <;> simp
lemma twist_xor (a b c : Bool) : twist (a.xor b) c=twist a c*twist b c := by cases a <;> cases b <;> cases c <;> simp
lemma twist_xor' (a b c : Bool) : twist a (b.xor c)=twist a b*twist a c := by cases a <;> cases b <;> cases c <;> simp

variable (p : α → Bool)
def parity : List α → Bool
  | [] => false
  | a :: L => (p a).xor (parity L)
include p
@[simp] lemma parity_nil : parity p [] = false := rfl
@[simp] lemma parity_cons (a) (L) : parity p (a::L)=(p a).xor (parity p L) := rfl
omit p in
lemma parity_map {β : Type*} (q : β → Bool) (f : α → β) (L : List α) : parity q (L.map f)=parity (q ∘ f) L := by
  induction L <;> simp_all

/-- Sum of signed shuffles, with a general continuation to keep momentum routing. -/
def divide : List α → (List α → List α → ℂ) → ℂ
  | [], h => h [] []
  | a :: L, h => divide L (fun A B => h (a::A) B) +
      divide L (fun A B => twist (p a) (parity p A) * h A (a::B))

lemma divide_congr {L : List α} {f g : List α → List α → ℂ}
    (h : ∀ A B, List.Perm (A++B) L → f A B=g A B) : divide p L f=divide p L g := by
  induction L generalizing f g with
  | nil => exact h [] [] (List.Perm.refl _)
  | cons a L ih =>
    unfold divide
    rw [ih (g:=fun A B => g (a::A) B) (fun A B H => h _ _ (H.cons a))]
    congr 1; exact ih fun A B H => congrArg _ (h _ _ (List.perm_middle.trans (H.cons a)))

lemma divide_zero (L : List α) : divide p L (fun _ _ => 0)=0 := by induction L <;> simp_all [divide]
lemma divide_add (L : List α) (f g : List α → List α → ℂ) :
    divide p L (fun A B => f A B+g A B)=divide p L f+divide p L g := by
  induction L generalizing f g with
  | nil => rfl
  | cons a L ih => unfold divide; simp only [mul_add]; rw [ih,ih]; abel

lemma divide_factor (L : List α) (f : List α → List α → ℂ) (c : ℂ) :
    divide p L (fun A B => c*f A B)=c * divide p L f := by
  induction L generalizing f with
  | nil => rfl
  | cons a L ih => unfold divide; simp_rw [mul_left_comm (twist ..) c]; rw [ih,ih,mul_add]

omit p in
lemma divide_map {β : Type*} (q : β → Bool) (f : α → β) (L : List α)
    (h : List β → List β → ℂ) : divide q (L.map f) h=divide (q ∘ f) L (fun A B => h (A.map f) (B.map f)) := by
  induction L generalizing h <;> simp_all [divide,parity_map]
end YM.MSBar.Super
