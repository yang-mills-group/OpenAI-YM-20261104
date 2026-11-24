import YM.RG11Proof.Rigidity.Lists

/-!
# List polarization by stripping one identical letter from the numerator
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Rigidity.Prism
open scoped BigOperators
open Function
variable {I : Type} [AddCommGroup I] [Module ℝ I]

structure Weight (F : List I → ℝ) : Prop where
  swappable {L t} (h : List.Perm L t) : F L=F t
  plus (a b : I) (L : List I) : F ((a+b)::L)=F (a::L)+F (b::L)
  ratio (s : ℝ) (a : I) (L : List I) : F ((s • a)::L)=s*F (a::L)

namespace Weight
variable {A B : List I→ℝ}
omit [AddCommGroup I] [Module ℝ I] in
private lemma move_book (a : I) (L T : List I) : List.Perm (a::(L++T)) (L++a::T) := List.perm_middle.symm
lemma reps (h : Weight A) (n : ℕ) (x y : I) (p : List I) :
    HasDerivAt (fun t : ℝ=> A (List.replicate n (x+t • y) ++ p)) ((n : ℝ)*A (List.replicate (n-1) x ++ y::p)) 0 := by
  induction n generalizing p with
  | zero=> simpa using (hasDerivAt_const (0:ℝ) (A p))
  | succ n ih=>
    simp_rw [List.replicate_succ,List.cons_append,h.plus,h.ratio]
    simp_rw [h.swappable (move_book x ..),h.swappable (move_book (I:=I) y ..)]
    have ht := (ih (x::p)).add ((hasDerivAt_id' (x:=(0:ℝ))).fun_mul (ih (y::p)))
    have he : (n:ℝ)*A (List.replicate (n-1) x ++ y :: x :: p) = (n:ℝ)*A (List.replicate n x ++ y::p) := by
      cases n with
      | zero=> simp
      | succ n=> simp only [Nat.add_sub_cancel,List.replicate_succ,List.cons_append]
                 rw [h.swappable (move_book x ..), h.swappable ((List.Perm.swap y x p).append_left (List.replicate n x))]
    simpa [Pi.add_def,he,Nat.cast_add,Nat.cast_one,add_mul] using ht

lemma from_diag (h : Weight A) (n : ℕ) (H : ∀ a, A (List.replicate n a)=0) (L : List I) (hl : L.length=n) : A L=0 := by
  suffices he : ∀ k, ∀ p : List I, k+p.length=n → ∀ a, A (List.replicate k a ++ p)=0 by simpa using he 0 L (by omega) 0
  -- induct on the tail p (introduce one arbitrary, from k+1 identical)
  intro k p; induction p generalizing k with
  | nil => intro hp; simp only [List.length_nil,add_zero] at hp; subst k; simpa using H
  | cons a p ih=>
    intro hp x
    have ht := h.reps (k+1) x a p
    simp_rw [ih (k+1) (by simp only [List.length_cons] at hp; omega), Nat.add_sub_cancel] at ht
    exact (mul_eq_zero.mp (ht.unique (hasDerivAt_const ..))).resolve_left (by positivity)

lemma polarize (n : ℕ) (h : Weight A) (H : Weight B) (he : ∀ a, A (List.replicate n a)= B (List.replicate n a))
    (L : List I) (hl : L.length=n) : A L=B L := by
  let F := A-B
  have hf : Weight F := ⟨fun ht=> by change A _-B _ = A _- B _; rw [h.swappable ht,H.swappable ht],
    fun a b L=> by simp only [F,Pi.sub_apply,h.plus,H.plus]; abel,
    fun a b L=> by simp only [F,Pi.sub_apply,h.ratio,H.ratio]; ring⟩
  exact sub_eq_zero.mp (hf.from_diag n (fun a=>sub_eq_zero.mpr (he a)) L hl)
end Weight
end YM.RG11.Rigidity.Prism
