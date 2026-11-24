import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Group
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Exponential symbol series with exchange grading

Convenient derivative-and-shuffle calculus. Over a discrete momentum group
these are the ordinary symmetric and Grassmann kernels. The symbol is
normalized to be the value of repeated left derivatives in the given order,
so no factorials upon applying a mode derivative. May include mark labels of
any parity as parameters.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Koszul
open Function Set Finset
variable {R : Type*} [CommRing R] {A B : Type*}

abbrev Sector (A : Type*) := A → Bool
abbrev Raw (A R : Type*) := List A → R
variable {F H : Raw A R}
def cross (p q : Bool) : R := if p && q then -1 else 1
@[simp] lemma cross_false (b:Bool) : (cross false b:R)=1:= by simp [cross]
@[simp] lemma cross_false' (b:Bool): (cross b false:R)=1:=by simp [cross]
@[simp] lemma cross_true : (cross true true:R)=-1:= rfl
lemma cross_comm (p q:Bool) : (cross p q : R)=cross q p:=by cases p <;> cases q <;> simp
lemma cross_cross (p q:Bool) : (cross p q : R)*cross p q=1:=by cases p <;> cases q <;> simp
lemma cross_right (p q c:Bool) : (cross p (q.xor c):R)=cross p q*cross p c:=by cases p <;> cases q <;> cases c <;> simp [Bool.xor]
lemma cross_left (p q c:Bool) : (cross (q.xor c) p:R)= cross q p * cross c p:=by rw [cross_comm,cross_right,cross_comm q,cross_comm c]

def degree (p : Sector A) : List A→Bool
  | []=>false
  | x::l=> (p x).xor (degree p l)
@[simp] lemma degree_nil (p : Sector A) : degree p []=false:=rfl
@[simp] lemma degree_cons (p : Sector A) x l : degree p (x::l)= Bool.xor (p x) (degree p l) := rfl
@[simp] lemma degree_join (p : Sector A) (l k : List A) : degree p (l++k)= (degree p l).xor (degree p k) := by
   induction l with
   | nil=>simp
   | cons x l IH=> simp [IH]

-- Left derivative

def D (x : A) : Raw A R →ₗ[R] Raw A R where
   toFun f l:= f (x::l)
   map_add' _ _:= rfl
   map_smul' _ _:= rfl
@[simp] lemma at_D (x) (f : Raw A R) l : D x f l=f (x::l):= rfl
lemma D_eval (x:A) (f:Raw A R) l : f (x::l) = D x f l:= rfl

def sign (p : Sector A) (q:Bool) : Raw A R →ₗ[R] Raw A R where
   toFun f l := cross q (degree p l)* f l
   map_add' f g:= by ext; exact mul_add ..
   map_smul' c f:= by ext; exact mul_left_comm ..
@[simp] lemma at_sign (p : Sector A) q (f:Raw A R) l : sign p q f l=cross q (degree p l)*f l:=rfl
variable (p : Sector A)
lemma sign_D (q:Bool) x (f:Raw A R) : D x (sign p q f) = (cross q (p x) : R) • sign p q (D x f) := by
    ext; simp only [at_D,at_sign,degree_cons,cross_right,mul_assoc,Pi.smul_apply,smul_eq_mul]
lemma sign_twice (q c:Bool) (f:Raw A R) : sign p q (sign p c f) = sign p (q.xor c) f := by
    ext; simp only [at_sign,cross_left,mul_assoc]
lemma signs_commute (q c:Bool) (f:Raw A R) : sign p q (sign p c f)=sign p c (sign p q f):= by rw [sign_twice,sign_twice,Bool.xor_comm]
@[simp] lemma sign_id (f:Raw A R) : sign p false f=f:= by ext; simp

/-- Supported coefficients (don't infer this from sign = id, no assumptions on field here). -/
def Pure (b:Bool) (f:Raw A R) := ∀ (l : List A), degree p l ≠ b → f l=0

namespace Pure
variable {p} {b c:Bool}
theorem from_nil (hf : Pure p b F) (h:b=true) : F []=0:= hf [] (by simp [h])
theorem add (hf : Pure p b F) (hg : Pure p b H) : Pure p b (F+H) := fun i hi=> by simp [hf i hi,hg i hi]
theorem zero : Pure p b (0:Raw A R) := fun _ _=> rfl
lemma smul (c : R) (h : Pure p b F) : Pure p b (c • F) := fun l hl => by simp [h l hl]
lemma sum (s : Finset B) {f : B→ Raw A R} (h : ∀ b'∈s, Pure p b (f b')) : Pure p b (∑ b∈s,f b) := by
    classical
    exact fun l hl=> by rw [Finset.sum_apply]; exact Finset.sum_eq_zero fun _ hx=> h _ hx l hl
lemma drop (x) (h : Pure p b F) : Pure p (b.xor (p x)) (D x F) := by
   intro i hi; refine h (x::i) ?_; rw [degree_cons]; cases hp:p x <;> cases hl:degree p i <;> cases b <;> simp_all [Bool.xor]
lemma signs (h : Pure p b F) q : sign p q F=(cross q b:R) • F := by
   funext x; by_cases hv:degree p x=b
   · simp [hv]
   simp [h x hv]
end Pure

/-- Equality on symbols includes Koszul exchange of any adjacent pair. -/
def Symm (f : Raw A R) := ∀ l i j r,
    f (l++(i::j::r)) = cross (p i) (p j) * f (l++(j::i::r))

namespace Symm
variable {p}
theorem drop (x) (h : Symm p F) : Symm p (D x F) := fun l i j r=> h (x::l) i j r
lemma commute (h : Symm p F) (x y:A): D x (D y F)=(cross (p y) (p x):R) • D y (D x F) := by ext l; exact h [] y x l
lemma zero : Symm p (0:Raw A R) := by intro _ _ _ _; simp
lemma add (h : Symm p F) (g : Symm p H) : Symm p (F+H) := fun l i j r=> by
   simp only [Pi.add_apply]; nth_rw 1 [h l i j r, g l i j r]; exact (mul_add ..).symm
lemma sum (s : Finset B) {f : B→ Raw A R} (h : ∀ b'∈s, Symm p (f b')) : Symm p (∑ b∈s,f b) := by
   classical
   induction s using Finset.induction_on with
   | empty => simpa using zero (R:=R) (p:=p)
   | insert a s ha ih => rw [Finset.sum_insert ha]; exact (h a (Finset.mem_insert_self ..)).add (ih (fun i hi=> h i (mem_insert_of_mem hi)))
lemma smul (c : R) (h : Symm p F) : Symm p (c • F) := fun l i j r=> by
   simp only [Pi.smul_apply,smul_eq_mul]; nth_rw 1 [h l i j r]; exact mul_left_comm ..
lemma neg (h: Symm p F) : Symm p (-F) := by simpa using smul (-1:R) h
lemma sub (h : Symm p F) (g : Symm p H) : Symm p (F-H) := by simpa only [sub_eq_add_neg] using add h (neg g)
lemma signs (h : Symm p F) q : Symm p (sign p q F) := by
   intro l i j r; rw [at_sign,h l i j r, at_sign]; simp only [degree_join,degree_cons,cross_right]; ring
lemma after (H : ∀ i, Symm p (D i F)) (H' : ∀ i j l, F (i::j::l)=cross (p i) (p j)*F (j::i::l)) : Symm p F := by
   intro l i j r; cases l with
   | nil=>exact H' ..
   | cons a l=> exact H _ l i j r
end Symm
-- Product: left derivative Leibniz extended uniquely on lists.
def times (u v : Raw A R) : Raw A R
  | [] => u [] * v []
  | x::w => times (D x u) v w + times (sign p (p x) u) (D x v) w
termination_by w => w.length
@[simp] lemma times_nil (u v : Raw A R) : times p u v []= u []*v []:= by rw [times]
lemma times_rule (u v : Raw A R) (x) :
    D x (times p u v)= times p (D x u) v + times p (sign p (p x) u) (D x v) := by ext l; rw [at_D,times,Pi.add_apply]
lemma ext_D {u v: Raw A R} (h : u []=v []) (hh : ∀ i,D i u=D i v): u=v := by funext l; cases l with | nil=> exact h | cons a l=> exact congr_fun (hh a) l
lemma times_add (u w v : Raw A R) : times p u (w+v)=times p u w+times p u v := by
   funext l; induction l generalizing u v w with
   | nil=>simp [mul_add]
   | cons a l IH=> simp only [D_eval a, map_add,times_rule, Pi.add_apply, IH]; abel
lemma add_times (u w v : Raw A R) : times p (w+v) u=times p w u+times p v u := by
   funext l; induction l generalizing u v w with
   | nil=>simp [add_mul]
   | cons a l IH=> simp only [D_eval a, map_add,times_rule, Pi.add_apply, IH]; abel
lemma times_smul (u v : Raw A R) (c:R) : times p u (c • v)=c • times p u v := by
   funext l; induction l generalizing u v with
   | nil=>simp [mul_left_comm]
   | cons a l IH=> simp only [D_eval a, map_smul,times_rule, Pi.add_apply,Pi.smul_apply, IH,smul_eq_mul, mul_add]
lemma smul_times (u v : Raw A R) (c:R) : times p (c • u) v=c • times p u v := by
   funext l; induction l generalizing u v with
   | nil=>simp [mul_assoc]
   | cons a l IH=> simp only [D_eval a, map_smul,times_rule, Pi.add_apply,Pi.smul_apply, IH,smul_eq_mul, mul_add]
lemma twisted_product (u v : Raw A R) (q:Bool) : sign p q (times p u v)=times p (sign p q u) (sign p q v) := by
   funext l; induction l generalizing u v with
   | nil=>simp
   | cons a l IH=>
      simp only [D_eval a (sign p q (times p u v)),D_eval a (times p _ _), times_rule, sign_D, signs_commute (f:=u) (c:=q), smul_times,times_smul,map_add,Pi.add_apply,Pi.smul_apply,smul_eq_mul] -- rw order
      simp only [← IH, at_sign]; ring
end YM.MS.Koszul
