import YM.MSbar.Super.Divide
import Mathlib.Tactic

/-!
# Supersymmetric tensors, left derivatives

Allow arbitrary formal Taylor series in the commuting and anticommuting variables.
Use shuffle product. Everything is type synonyms for functions -- addition and
complex scalar multiplication on the unrestricted functions. Keep grading and symmetry
as separate properties. This calculus includes the scalar vacuum coefficients.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Super
open Function Finset
open scoped BigOperators
variable {α β : Type*}
abbrev Term (α : Type*) := List α → ℂ
def peel (x : α) (f : Term α) : Term α := fun L => f (x::L)
@[simp] lemma peel_apply (x : α) (f : Term α) (L) : peel x f L = f (x::L) := rfl
lemma peel_add (x : α) (f g : Term α) : peel x (f+g)=peel x f+peel x g := rfl
lemma peel_sub (x : α) (f g : Term α) : peel x (f-g)=peel x f-peel x g := rfl
lemma peel_neg (x : α) (f : Term α) : peel x (-f)=-peel x f := rfl
lemma peel_smul (x : α) (c : ℂ) (f : Term α) : peel x (c • f)=c • peel x f := rfl
@[simp] lemma peel_zero (x : α) : peel x 0=0 := rfl
lemma peel_sum (x : α) (f : β → Term α) (s : Finset β) : peel x (∑ b ∈ s, f b)=∑ b ∈ s,peel x (f b) := by ext1; simp

def scalar (c : ℂ) : Term α
 | [] => c
 | _::_ => 0
@[simp] lemma scalar_nil (c : ℂ) : scalar (α:=α) c []=c := rfl
@[simp] lemma peel_scalar (x : α) (c : ℂ) : peel x (scalar c)=0 := rfl

def letter [DecidableEq α] (x : α) : Term α
 | [] => 0
 | a :: L => if a=x then scalar 1 L else 0
@[simp] lemma letter_nil [DecidableEq α] (x : α) : letter x []=0 := rfl
lemma peel_letter [DecidableEq α] (x a : α) : peel a (letter x)=if a=x then scalar 1 else 0 := by
  ext; split_ifs <;> simp_all [letter]
@[simp] lemma peel_letter_self [DecidableEq α] (x : α) : peel x (letter x)=scalar 1 := by rw [peel_letter,if_pos rfl]

variable (p : α → Bool)
/-- Condition just on the parity degree. Stronger integer-statistic grading can be used separately. -/
def Grade (b : Bool) (f : Term α) : Prop := ∀ L, parity p L ≠ b → f L=0
/-- Supersymmetry, phrased with adjacent transpositions -- covers Bose and Fermi at once. -/
def Ordered (f : Term α) : Prop := ∀ A (x y : α) L,
  f (A ++ x :: y :: L) = twist (p x) (p y) * f (A ++ y :: x :: L)

@[simp] lemma parity_append (A B : List α) : parity p (A++B)=(parity p A).xor (parity p B) := by
  induction A <;> simp_all
variable {p}
lemma parity_perm {A B : List α} (h : A.Perm B) : parity p A=parity p B := by
  induction h with
  | nil => rfl
  | cons _ _ e => simp [e]
  | swap x y L => simp only [parity_cons,← Bool.xor_assoc]; rw [Bool.xor_comm (p x)]
  | trans _ _ e f => exact e.trans f

variable {f g : Term α} {r : Bool}
lemma Grade.degree (h : Grade p r f) {L} (he : f L ≠ 0) : parity p L = r := Classical.byContradiction (he ∘ h L)
@[simp] lemma grade_zero : Grade p r 0 := fun _ _ => rfl
lemma Grade.add (h : Grade p r f) (H : Grade p r g) : Grade p r (f+g) := by intro L hn; simp [h L hn,H L hn]
lemma Grade.sub (h : Grade p r f) (H : Grade p r g) : Grade p r (f-g) := by intro L hn; simp [h L hn,H L hn]
lemma Grade.neg (h : Grade p r f) : Grade p r (-f) := by intro L hn; simp [h L hn]
lemma Grade.smul (h : Grade p r f) (c : ℂ) : Grade p r (c • f) := by intro L hn; simp [h L hn]
lemma Grade.sum {f : β → Term α} {s : Finset β} (h : ∀ b∈s,Grade p r (f b)) : Grade p r (∑ b∈s,f b) := by intro L hn; simp [sum_eq_zero (fun i hi => h i hi L hn)]
@[simp] lemma grade_scalar (c) : Grade p false (scalar c) := by rintro (_|_) H <;> simp_all [scalar]
lemma Grade.peel (h : Grade p r f) (x : α) : Grade p ((p x).xor r) (peel x f) := by
  intro L e; apply h; intro he; apply e; simp [←he]
@[simp] lemma grade_letter [DecidableEq α] (x : α) : Grade p (p x) (letter x) := by rintro (_|⟨a,_|⟨b,L⟩⟩) H <;> simp_all [letter,scalar]; rintro rfl; simp at H

@[simp] lemma ordered_zero (p : α → Bool) : Ordered p 0 := by simp [Ordered]
lemma Ordered.add (h : Ordered p f) (H : Ordered p g) : Ordered p (f+g) := by intro A x y L; simp only [Pi.add_apply]; rw [h A x y,H A x y,mul_add]
lemma Ordered.sub (h : Ordered p f) (H : Ordered p g) : Ordered p (f-g) := by intro A x y L; simp only [Pi.sub_apply]; rw [h A x y,H A x y,mul_sub]
lemma Ordered.neg (h : Ordered p f) : Ordered p (-f) := by intro A x y L; simp only [Pi.neg_apply]; rw [h A x y,mul_neg]
lemma Ordered.smul (h : Ordered p f) (c : ℂ) : Ordered p (c • f) := by intro A x y L; simp only [Pi.smul_apply,smul_eq_mul]; rw [h A x y,mul_left_comm]
lemma Ordered.sum {f : β → Term α} {s : Finset β} (h : ∀ b∈s,Ordered p (f b)) : Ordered p (∑ b∈s,f b) := by
  intro A x y L; simp only [Finset.sum_apply,mul_sum]; exact sum_congr rfl fun i hi => h i hi A x y L
lemma Ordered.peel (h : Ordered p f) (x) : Ordered p (peel x f) := fun A y z L => h (x::A) y z L
lemma Ordered.exchange (h : Ordered p f) (x y : α) : Super.peel y (Super.peel x f)=twist (p x) (p y) • Super.peel x (Super.peel y f) := by ext L; exact h [] x y L
lemma ordered_intro {f : Term α} (h : ∀ x,Ordered p (peel x f))
    (H : ∀ x y,peel y (peel x f) = twist (p x) (p y) • peel x (peel y f)) : Ordered p f := by
  rintro (_|⟨a,A⟩) x y L
  · exact congrFun (H x y) L
  · exact h a A x y L
@[simp] lemma ordered_scalar (c) : Ordered p (scalar c) := by apply ordered_intro <;> simp [peel_scalar]
@[simp] lemma ordered_letter [DecidableEq α] (x : α) : Ordered p (letter x) := by
  apply ordered_intro
  · intro a; rw [peel_letter]; split <;> simp
  · intro a b; rw [peel_letter,peel_letter]; split_ifs <;> simp [peel_scalar]
end YM.MSBar.Super
