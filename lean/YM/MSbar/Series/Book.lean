import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Complex.BigOperators
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Tactic

/-! Coefficientwise identities for amplitude recursion without assumptions on uniform asymptotics
in orders. No analytic function of coupling or ℏ involved. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Category
open Function Set Finset
open scoped BigOperators Classical

abbrev Form (X: Type*) := ℕ→X
variable {X Y Z : Type*} [AddCommGroup X][Module ℂ X][AddCommGroup Y][Module ℂ Y][AddCommGroup Z][Module ℂ Z] {f h: Form X} {g k:Form Y} {i j n m:ℕ} {A:X→ₗ[ℂ] Y} {B:X→ₗ[ℂ] Y→ₗ[ℂ] Z}

def act (A:X→ₗ[ℂ] Y): Form X→ₗ[ℂ] Form Y := {
    toFun:= fun f i=> A (f i)
    map_add':= fun _ _=> funext fun _=> map_add ..
    map_smul':= fun _ _ => funext fun _=> map_smul ..}
@[simp]lemma act_val : act A f i= A (f i):=rfl

def dilation (A:X →ₗ[ℂ] Y) : Form X→ℕ → Y
    | _,0=>0
    | f,n+1=>A (f n)
def sea (A:X→ₗ[ℂ] Y): Form X →ₗ[ℂ] Form Y := {
    toFun:= dilation A
    map_add':= fun f g=> funext fun i=> by cases i <;> simp [dilation]
    map_smul':= fun c f=> funext fun i=> by cases i <;> simp [dilation] }
@[simp]lemma sea_zero : sea A f 0=0:=rfl
@[simp]lemma sea_pos : sea A f (i+1)=A (f i):=rfl

def knot (B:X→ₗ[ℂ] Y→ₗ[ℂ] Z) : Form X→ₗ[ℂ] Form Y →ₗ[ℂ] Form Z :=
   LinearMap.mk₂ ℂ (fun x y n=> ∑ p∈Finset.antidiagonal n,B (x p.1) (y p.2))
    (fun f g h=> by ext n; simp [sum_add_distrib]) (fun c f g=>by ext n; simp [smul_sum])
    (fun f g h=> by ext n; simp [sum_add_distrib]) (fun c f g=>by ext n; simp [smul_sum])
@[simp]lemma knotted : knot B f g n= ∑ p∈Finset.antidiagonal n,B (f p.1) (g p.2):=rfl

abbrev Prior {X:Type*} (n:ℕ) (x y:Form X):= ∀ i≤ n,x i=y i
namespace Prior
omit [Module ℂ X] [AddCommGroup X] in
lemma here (a: Form X): Prior i a a:=fun _ _=>rfl
omit [Module ℂ X] [AddCommGroup X] in
lemma symm (hp:Prior n f h):Prior n h f:=fun _ hx=> Eq.symm (hp _ hx)
omit [Module ℂ X] [AddCommGroup X] in
lemma trans {y} (a:Prior i f h)(b:Prior i h y):Prior i f y:=fun _ hn=> (a _ hn).trans (b _ hn)
omit [Module ℂ X] [AddCommGroup X] in
lemma value (a: Prior i f h): f i=h i:= a _ le_rfl
omit [Module ℂ X] [AddCommGroup X] in
lemma restrict (a:Prior i f h)(hu:j ≤ i):Prior j f h:=fun _ h'=>a _ (h'.trans hu)
lemma move (a:Prior i f h)(A:X→ₗ[ℂ] Y):Prior i (act A f) (act A h):=fun _ hx=>congr_arg A (a _ hx)
lemma flow (a:Prior i f h)(A:X→ₗ[ℂ] Y):Prior (i+1) (sea A f) (sea A h):=fun j hx=> by cases j with | zero=> rfl | succ j=>rw [sea_pos,sea_pos,a _ (by omega)]
lemma glue (a:Prior i f h)(b:Prior i g k)(B:X→ₗ[ℂ] Y→ₗ[ℂ] Z):Prior i (knot B f g) (knot B h k):= fun j hj=> by simp_rw [knotted]; apply sum_congr rfl; rintro ⟨x,y⟩ H; obtain hxy : x+y=j:= Finset.mem_antidiagonal.mp H; dsimp; rw [a _ (by omega),b _ (by omega)]
omit [Module ℂ X] in
lemma adding {x y:Form X}(a:Prior i f h)(b:Prior i x y): Prior i (f+x) (h+y):= fun j hj=> congr_arg₂ (·+·) (a j hj) (b j hj)
lemma scaling (a:Prior i f h)(c:ℂ): Prior i (c • f) (c • h):= fun j hj=> congr_arg (fun x=>c • x) (a j hj)
end Prior

def chill {X:Type*}[Zero X](i:ℕ)(f:Form X):Form X:=fun j=>if j ≤ i then f j else 0
abbrev Cap {X:Type*} [Zero X](n:ℕ)(f:Form X):=∀ i:ℕ,n < i → f i=0
lemma just {X:Type*}[Zero X](i:ℕ)(f:Form X): Prior i (chill i f) f := fun j hj=> if_pos hj
lemma still {X:Type*}[Zero X](i:ℕ)(f:Form X): Cap i (chill i f) := fun j hj=> if_neg (not_le.mpr hj)
namespace Cap
omit [Module ℂ X] in
lemma carry (a:Cap i f)(h:i≤j): Cap j f:= fun _ hj=> a _ (h.trans_lt hj)
lemma move (a:Cap i f)(A:X→ₗ[ℂ] Y): Cap i (act A f):= fun j hj=> by simp [a j hj]
lemma step (a:Cap i f)(A:X→ₗ[ℂ] Y): Cap (i+1) (sea A f):= fun j hj=> by cases j with | zero=> omega | succ j=> simp [a j (by omega)]
lemma spin (a:Cap i f)(b:Cap j g)(B:X→ₗ[ℂ] Y→ₗ[ℂ] Z): Cap (i+j) (knot B f g) := fun m hm=> by rw [knotted]; apply sum_eq_zero; rintro ⟨x,y⟩ H; obtain hxy:x+y=m:=Finset.mem_antidiagonal.mp H; dsimp; by_cases hx: i<x; rw [a _ hx,map_zero]; rfl; rw [b _ (by omega),map_zero]
omit [Module ℂ X] in
lemma add (a:Cap i f)(b:Cap i h):Cap i (f+h):=fun t ht=>by simp [a t ht,b t ht]
lemma scale (a:Cap i f)(c:ℂ):Cap i (c•f):=fun t ht=> by simp [a t ht]
omit [Module ℂ X] in
lemma sub (a:Cap i f)(b:Cap i h):Cap i (f-h):=fun t ht=>by simp [a t ht,b t ht]
end Cap
end YM.MSbar.Category
