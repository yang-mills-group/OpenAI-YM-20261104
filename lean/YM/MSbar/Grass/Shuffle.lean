import Mathlib.Data.Complex.BigOperators
import Mathlib.Algebra.CharP.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! Supercommutative field Taylor series. No finiteness needed on any index; not a nonperturbative
convergence assumption. Coefficients include derivatives (not divided); exponential factorials
live in the diagram convention. Every letter is a Fourier mode/polarization later. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Super
open Function List Finset
open scoped Classical BigOperators

abbrev Bit := ZMod 2
def sign (i j: Bit): ℂ := if i=1 ∧ j=1 then -1 else 1
abbrev word (T : Type*) := List T
abbrev Series (T : Type*) := word T → ℂ
variable {T : Type*} (p : T → Bit) {d e c j : Bit}

@[simp]lemma sign_zero : sign c 0=1:= by simp [sign]
lemma braid (d c) : sign d c=sign c d:= by simp [sign,and_comm]
@[simp]lemma sign_zero_left : sign 0 c=1:=by rw [braid,sign_zero]
@[simp]lemma sign_self (i j): sign i j * sign i j=1:=by unfold sign; split_ifs <;> norm_num
lemma bit_cases (d:Bit): d=0∨d=1:= by decide +revert
lemma cycle (i j:Bit): i+(i+j)=j:=by rcases bit_cases i with rfl|rfl <;> rcases bit_cases j with rfl|rfl <;> decide
lemma sign_add (d c j : Bit): sign (d+c) j=sign d j*sign c j:=by
    have h : (1:Bit)+1=0:=by decide
    rcases bit_cases d with rfl|rfl <;> rcases bit_cases c with rfl|rfl <;> rcases bit_cases j with rfl|rfl <;> simp [h]
lemma sign_add_right (d c e) : sign d (c+e)=sign d c*sign d e:=by rw [braid,sign_add,braid c,braid e]

def oddity (p:T→Bit)(v : word T) := (v.map p).sum
@[simp]lemma oddity_nil : oddity p []=0:=rfl
@[simp]lemma oddity_cons (a:T)(v : word T) : oddity p (a::v)= p a+oddity p v:=by simp [oddity]
lemma oddity_plus (a b : word T): oddity p (a++b)=oddity p a+oddity p b:=by simp [oddity]

/-- Split recursion computes sum over all partitions of ordered labelled legs,
including signs for the crossings. Can use an integrand with correlator depending on both legs. -/
def split (F : word T → word T → ℂ) : Series T
  | [] => F [] []
  | a::v => split (fun s t=> F (a::s) t) v + split (fun s t=> sign (p a) (oddity p s)*F s (a::t)) v
termination_by v => v.length
-- check rec syntax recursive arguments implicit p?

variable {F G : word T→word T→ℂ}
@[simp]lemma split_nil : split p F []= F [] []:=by rw [split]
lemma split_next (v : word T)(a:T):split p F (a::v)=split p (fun s t=> F (a::s) t) v + split p (fun s t=> sign (p a) (oddity p s)*F s (a::t)) v:=by rw [split]

lemma split_add : split p (F+G) = split p F + split p G := by
    funext v; induction v generalizing F G with
    | nil=> simp
    | cons a s ih =>
       rw [Pi.add_apply,split_next,split_next,split_next]; simp_rw [Pi.add_apply,mul_add]
       let f (F:word T→word T→ℂ):=fun s t=>F (a::s) t; let g (F:word T→word T→ℂ):= fun s t=>sign (p a) (oddity p s)*F s (a::t)
       change split p (f F+f G) s+split p (g F+g G) s=_; rw [ih,ih]; dsimp only [f,g,Pi.add_apply]; ring
lemma split_scale (c : ℂ): split p (c • F)= c • split p F:=by
    funext v; induction v generalizing F with
    | nil =>simp
    | cons a s ih=>
       rw [Pi.smul_apply,split_next,split_next]; simp_rw [Pi.smul_apply,smul_eq_mul]
       let f (s t):=F (a::s) t; let g (s t):=sign (p a) (oddity p s)*F s (a::t)
       simp_rw [mul_left_comm (sign (p a) _) c]; change split p (c • f) s + split p (c • g) s = c* _; rw [ih,ih]; exact (mul_add ..).symm
@[simp]lemma split_zero : split p 0=0:= by
   funext v; induction v with
   | nil=> simp
   | cons a s ih=> rw [split_next]; simp only [Pi.zero_apply,mul_zero]; change split p 0 s+split p 0 s=0; rw [ih]; simp
lemma split_sum {ι : Type*} (F:ι→word T→word T→ℂ) (I:Finset ι) : split p (∑ i∈I,F i)=∑ i∈I,split p (F i):=by induction I using Finset.induction_on with | empty=> simp | insert i I he ih=> rw [Finset.sum_insert he,Finset.sum_insert he,split_add,ih]
lemma split_clear {v:word T}(he:∀ u w,(u++w).Perm v → F u w=0): split p F v=0:=by
   induction v generalizing F with
   | nil=> simpa using he [] [] List.Perm.rfl
   | cons a v ih=>
      rw [split_next,ih (F:=fun u w=> F (a::u) w) (fun u w h=> he _ _ (h.cons a)),ih,zero_add]
      intro u w h; rw [he u (a::w) ((List.perm_middle).trans (h.cons a)),mul_zero]
lemma split_change {v:word T}(he:∀ u w,(u++w).Perm v → F u w=G u w): split p F v=split p G v:=by
   apply sub_eq_zero.mp; have hv := split_clear p (F:=F+(-1:ℂ) • G) (v:=v) (by intro a b ha; simp [he a b ha])
   rw [split_add,split_scale] at hv; simpa [sub_eq_add_neg] using hv
end YM.MSbar.Super
