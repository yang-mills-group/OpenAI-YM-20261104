import YM.XSpace.Playing
import YM.XSpace.Passage

/-!
# Recursively normalize all positive orders with fixed position tests

The derivative is at the **actual finite-regulator solution**, same bounded
inverse at every step. Compatible if zeroth solution is. Uniqueness.
`solves` for all cameras, independent of external comparison. Exports
as pseudosubstitution on arrays (fixed coupling here!).
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Normalize
open Function Set Filter Maxwell Maxwell.Free Maxwell.Wick MeasureTheory PowerSeries Fray
open scoped BigOperators Topology Classical ContDiff
variable {G:Gauge} {d l:ℕ}

lemma aboutFrames (A: Screen G d) (p q: Pick G d) (R:Reports G d) (hl:l≠0) (h:∀ i<l,p i=q i): A.D (realm (deck p) R l)- A.D (realm (deck q) R l)= slope A (q 0) (R 0) (p l-q l):=by
  rw [← map_sub,deviates _ _ _ hl (fun i hi=>?_),pos_decked p hl,pos_decked q hl, coeff_zero_eq_constantCoeff_apply,const_deck]; rfl
  rw [decked,decked,pulling,pulling,h i hi]

namespace Screen

def Solved (A:Screen G d) (T:Pick G d) (R:Reports G d) :Prop:= ∀ l:ℕ,A.D (realm (deck T) R l)= if l=0 then A.D (reference G d) else 0
variable (A:Screen G d) (C: Change G d) (R:Reports G d)
-- offbranch not used. Select at every order, `roll` records derivative cost algebraically instead of numeric recurrence.
private def routine (l:ℕ) (T : ∀ i < l, Change G d) : Change G d :=
  let S : Pick G d:= fun j=> if h:j<l then T j h else 0
  if l=0 then C else (slope A C (R 0)).leftInverse (-(A.D (realm (deck S) R l)))

def shift : Pick G d:= fun i=> Nat.strongRecOn i (fun j g=> routine A C R j g)

def blind (S:Pick G d) (i:ℕ): Pick G d:= fun j=> if j < i then S j else 0
lemma blind_low (S:Pick G d) (i:ℕ): ∀ j < i, blind S i j=S j:= fun _ h=> if_pos h
lemma blind_at (S:Pick G d) (i:ℕ): blind S i i=0:= if_neg (lt_irrefl _)
lemma roll (l:ℕ): shift A C R l= if l=0 then C else (slope A C (R 0)).leftInverse (-A.D (realm (deck (blind (shift A C R) l)) R l)):=by
  unfold shift; conv_lhs=> rw [Nat.strongRecOn_eq]
  simp only [routine,dite_eq_ite]; rfl
@[simp] lemma shift_zero : shift A C R 0 = C:= (roll A C R 0).trans (if_pos rfl)

lemma bare_price (T:Pick G d) (hl:l≠0) (h:Solved A T R) : slope A (T 0) (R 0) (T l) = -(A.D (realm (deck (blind T l)) R l)):=by
  have he:= aboutFrames A T (blind T l) R hl (fun i hi=> (blind_low T l i hi).symm); rw [blind_at, blind_low _ l _ (Nat.pos_of_ne_zero hl), h l, if_neg hl,zero_sub,sub_zero] at he; exact he.symm
lemma constit (T:Pick G d) (h0:SetEq A (T 0) (R 0)) (H:∀ l:ℕ,l≠0→ slope A (T 0) (R 0) (T l) = -(A.D (realm (deck (blind T l)) R l))) : A.Solved T R:=by
  intro l; split_ifs with hg
  · subst l; rw [rest,coeff_zero_eq_constantCoeff_apply, const_deck]; exact h0
  have hh:= aboutFrames A T (blind T l) R hg (fun i hi=> (blind_low T l i hi).symm); rw [blind_low _ l _ (Nat.pos_of_ne_zero hg),blind_at,sub_zero,H l hg] at hh; exact (sub_eq_iff_eq_add.mp hh).trans (neg_add_cancel ..)
lemma rightInverse_of {U:Change G d→ₗ[ℝ] Change G d} (h:Bijective U) (p:Change G d): U (U.leftInverse p)=p:=by
  obtain ⟨p,rfl⟩:= h.surjective p; rw [LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr h.injective)]
theorem solving (h:SetEq A C (R 0)) (H:Bijective (slope A C (R 0))): A.Solved (A.shift C R) R:= by
  refine A.constit R _ ((shift_zero ..).symm ▸ h) (fun l hl=> ?_); rw [shift_zero, roll A C R l, if_neg hl,rightInverse_of H]
variable {A C R}
lemma shift_unique (A:Screen G d) (R:Reports G d) (u v:Pick G d) (h0:u 0=v 0) (he: A.Solved u R) (H:A.Solved v R) (h:Injective (slope A (u 0) (R 0))): u=v:=by
  ext1 l; induction l using Nat.strong_induction_on with
  | h i hi =>
    by_cases hq:i=0; subst i; exact h0
    have hs:= aboutFrames A v u R hq (fun i h=> (hi i h).symm); rw [he _, H _,sub_self] at hs; exact (sub_eq_zero.mp (h (Eq.trans hs.symm (map_zero _).symm))).symm

lemma shadow {T:Pick G (d+1)} {Q:Reports G (d+1)} {B:Screen G (d+1)} (he:A.Next B) (ht:B.Solved T Q): A.Solved (fun l=> fell d (T l)) (fun i=> recruit (step d) (Q i)):=by
  intro l; simp only [← tail_free (deck T) (deck _) (nest _ _ (fun _=>rfl)) Q,← he _,ht l]; split_ifs; · exact he _
  exact map_zero _
end Screen
end YM.XSpace.Normalize
