import YM.RG11Proof.Rigidity.Lists

/-!
# Removing endpoint-endpoint lines in test words

Core pair recursion with endpoints marked (all ordinary, repeated situs
forbidden by `line`; not attempting to add new local Wick operators as
admitted testers).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Rigidity
open Maxwell.Free
open scoped BigOperators

variable {I R A : Type*} [CommSemiring R]

lemma pulls_comm [AddCommMonoid A] (p : List I) {J : Type*} (u : List J) (f : I → List I → J → List J → A) :
    pulls p (fun i l=> pulls u (f i l))=pulls u (fun j r=> pulls p (fun i l=> f i l j r)) := Finset.sum_comm

lemma pulls_triple [AddCommMonoid A] (p : List I) (f : I → I → I → List I → A) :
   pulls p (fun a r=> pulls r (fun b s=> pulls s (fun c l=> f a b c l))) =
   pulls p (fun b r=> pulls r (fun c s=> pulls s (fun a l=> f a b c l))) := by
  rw [pulls_twice p (fun a b s=> pulls s (fun c l=> f a b c l))]
  apply pulls_congr; intro i; exact pulls_twice ..

namespace Strip
-- two racks. Primary word L on right. Internal endpoint-endpoint E or to the
-- primary K.
def grade (E K : I → I → R) : (u L : List I) → R
  | [],L=> pairCost K L
  | a::p,L=> (∑ i : Fin p.length, E a (p.get i) * grade E K (p.eraseIdx i.val) L) +
      pulls L (fun b r=> K a b * grade E K p r)
termination_by u _=> u.length
decreasing_by
  · apply lt_trans (pulls_short _) (by simp)
  · simp

lemma grade_cons (E K : I → I → R) (a : I) (p L : List I) :
    grade E K (a::p) L = pulls p (fun b r=> E a b * grade E K r L)+pulls L (fun b r=> K a b * grade E K p r) := by rw [grade]; rfl
lemma grade_nil (E K : I → I → R) (L : List I) : grade E K [] L=pairCost K L := by rw [grade]

lemma identical (K : I → I → R) (p L : List I) : grade K K p L=pairCost K (p++L) := by
  induction h : p.length using Nat.strong_induction_on generalizing p L with
  | h n ih =>
    subst n; cases p with
    | nil => exact grade_nil ..
    | cons a p =>
      rw [grade_cons, List.cons_append,pair_step,pulls_append]; congr 1
      all_goals apply pulls_congr; intro i
      · rw [ih _ (lt_trans (pulls_short i) (by simp)) _ _ rfl]
      rw [ih _ (by simp) p _ rfl]

lemma switches (E K : I → I → R) (he : ∀ i j, E i j=E j i) {p u : List I}
    (hp : List.Perm p u) (L : List I) : grade E K p L=grade E K u L := by
  induction h : p.length using Nat.strong_induction_on generalizing p u L with
  | h n ih=>
    induction hp generalizing L with
    | nil => rfl
    | @cons a p u hp _ =>
      simp_rw [grade_cons]
      congr 1
      · exact pulls_perm hp _ (fun i _ _ ht hh=> congr_arg (E a i * ·) (ih _ (by simp only [List.length_cons] at h; omega) hh _ rfl))
      apply pulls_congr; intro i; rw [ih p.length (by simp only [List.length_cons] at h; omega) hp _ rfl]
    | swap a b l =>
      simp_rw [grade_cons,pulls_cons]
      simp_rw [grade_cons,mul_add,pulls_add,← pulls_mul]
      -- expand *next* endpoint and rearrange into five cases.
      rw [pulls_twice l (fun i j r=>E b i*(E a j*grade E K r L)),
        pulls_twice L (fun i j r=>K b i*(K a j*grade E K l r)),
        pulls_comm L l (fun i p j r=> K b i*(E a j*grade E K r p)),
        pulls_comm l L (fun i p j r=> E b i*(K a j*grade E K p r)),he b a]
      simp_rw [show ∀ i j w, E b i*(K a j * w)= K a j*(E b i*w) from fun _ _ _=> mul_left_comm ..,
        show ∀ i j w, K b i*(E a j*w)= E a j*(K b i*w) from fun _ _ _=>mul_left_comm ..,
        show ∀ i j w, K b i*(K a j*w)= K a j*(K b i*w) from fun _ _ _=>mul_left_comm ..,
        show ∀ i j w, E b i*(E a j*w)= E a j*(E b i*w) from fun _ _ _=>mul_left_comm ..]; ac_rfl
    | trans hp hu hP hU => exact (hP _ h).trans (hU _ (hp.length_eq ▸ h))

end Strip
end YM.RG11.Rigidity
