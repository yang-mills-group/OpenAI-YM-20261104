import YM.Next.MAXWELL.Pulls

/-!
# Re-orderable word tests

For the RG11 detector problem. We use the actual list implementation of Wick's
rule (`Free.bag_rec`, with zero same-vertex kernel) so we can remove endpoints
from *words*, without sorting graphs or taking factorial quotients.
-/

set_option autoImplicit false
noncomputable section
namespace YM.RG11.Rigidity
open Maxwell.Free
open scoped BigOperators

variable {I J R S : Type*} [CommSemiring R]

section pulls
variable [AddCommMonoid S]

lemma pulls_add (l : List I) (f g : I → List I → S) :
    pulls l (fun a r => f a r + g a r) = pulls l f + pulls l g := Finset.sum_add_distrib
lemma pulls_mul (l : List I) (f : I → List I → R) (a : R) :
    pulls l (fun b r => a * f b r) = a * pulls l f := (Finset.mul_sum ..).symm

lemma pulls_perm {l t : List I} (h : List.Perm l t) (f : I → List I → S)
    (H : ∀ i {l' t' : List I}, l'.length < l.length → List.Perm l' t' → f i l' = f i t') :
    pulls l f = pulls t f := by
  induction h generalizing f with
  | nil => rfl
  | cons a h ih =>
    rw [pulls_cons,pulls_cons,H a (by simp) h,
      ih (fun b u => f b (a::u)) (fun i _ _ ht hp => H i (by simpa using ht) (.cons a hp))]
  | swap a b l =>
    rw [pulls_cons,pulls_cons,pulls_cons,pulls_cons]
    rw [add_left_comm]
    apply congr_arg (_ + ·); apply congr_arg (_ + ·); apply pulls_congr
    intro i
    exact H _ (by simp only [List.length_cons]; have := pulls_short i; omega) (.swap ..)
  | trans h g ih ik =>
    rw [ih f H,ik f (fun i _ _ ht hp => H i (by simpa only [h.length_eq] using ht) hp)]

end pulls

lemma pair_perm (K : I → I → R) (hK : ∀ i j, K i j = K j i) {l t : List I}
    (h : List.Perm l t) : pairCost K l = pairCost K t := by
  induction hn : l.length using Nat.strong_induction_on generalizing l t with
  | h n ih =>
    induction h with
    | nil => rfl
    | cons a h _ =>
      rw [pair_step,pair_step]
      apply pulls_perm h _
      intro i u v hu hv; rw [ih _ (by simp only [List.length_cons] at hn; omega) hv rfl]
    | swap a b l =>
      simp_rw [pair_step,pulls_cons]
      -- constant pair is symmetric; two disjoint pairs are symmetric by double pull.
      rw [hK b a]; apply congr_arg (K a b * pairCost K l + ·)
      simp_rw [pair_step, ← pulls_mul]
      rw [pulls_twice l (fun x y p => K b x * (K a y * pairCost K p))]
      simp [mul_left_comm]
    | trans h g hfg i => exact (hfg hn).trans (i (h.length_eq ▸ hn))

end YM.RG11.Rigidity
