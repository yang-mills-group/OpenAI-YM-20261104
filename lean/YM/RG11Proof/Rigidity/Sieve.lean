import YM.RG11Proof.Rigidity.Prune

/-!
# Screen all endpoint-endpoint lines
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Rigidity
open palette Strip Maxwell.Free Function Crowd
open scoped BigOperators Classical

abbrev Ear := Foil×E4
def hear {G : Gauge} (i : Ear) : G.ColorIndex → Pig G := toss i.1 i.2

variable {G : Gauge} {S : Finset E4} {W : Crowd G}

lemma blank (hW : Blind S W) (L : List Panel) (h : Journey Prod.snd S L) (r : ℝ) :
    deck (hear (G:=G)) L (fun p=> W.asks (fun u=> rate line line p u r))=0 := by
  induction ht : L.length using Nat.strong_induction_on generalizing L r S W with
  | h n ih=>
    let f (t : ℝ) (p : Word G) := W.asks fun u=> rate line line p u t
    let Φ (t : ℝ) := deck hear L (f t)
    have hf (t p) : HasDerivAt (fun t=>f t p) (1/2*nick line (f t) p) t := by
      unfold nick f pulls; simp_rw [← ask_mul, ← ask_sum]
      have hh : ∀ (W : Crowd G), HasDerivAt (fun t=> W.asks (fun u=> rate line line p u t))
          (W.asks (fun u=>1/2*nick line (fun r=>rate line line r u t) p)) t := by
        intro W; induction W with
        | nil=> exact hasDerivAt_const ..
        | cons a l ih=> simp only [ask_one]; exact ((nick_rate (K:=line) line_sym p a.2 t).const_mul _).add ih
      rw [← ask_mul]
      exact hh _
    have hz t : HasDerivAt Φ 0 t := by
      have hs : deck hear L (fun p=>1/2*nick line (f t) p) = 0 := by
        have he := trims (hear (G:=G)) line (fun i j=>beam (i.2-j.2) i.1 j.1) line_sym (fun i j _ _=> toss_line i.1 j.1 _ _ _ _) Prod.snd L (f t) ?_ S h ?_
        · unfold deck at *; rw [palette.mul _ _ (1/2),he,mul_zero]
        · intro l u hl; unfold f; congr 1; funext r; unfold rate; exact switches _ _ (fun a b=> by rw [line_sym a b]) hl r
        · intro p hp hpp
          exact ih _ (by omega) hW _ hpp _ rfl
      rw [← hs]; unfold Φ; unfold deck
      suffices hv : ∀ L : List (Dye G.ColorIndex (Pig G)), ∀ f : ℝ → Word G→ℝ, ∀ g : Word G→ℝ,
          (∀ p, HasDerivAt (fun t=> f t p) (g p) t) → HasDerivAt (fun t=> palette L (f t)) (palette L g) t from hv _ _ _ (hf t)
      intro L; induction L with
      | nil=> intro f g hg; exact hg _
      | cons a L ih=> intro f g hg; simp_rw [palette.cons]; apply HasDerivAt.fun_sum; intro i _; exact ih _ _ (fun p=>hg _)
    have he : Φ 1=0 := by
      unfold Φ f rate
      simp_rw [one_mul,identical]
      have hg := palette.sums_read L W meter
      have hP : deck hear L (fun p=> W.asks (fun l=> pairCost (ι:=Pig G) line (p++l))) =
        deck hear L.reverse (fun p=> W.asks (fun l=> pairCost line (p++l))) := by
        refine palette.deck_perm (Q:=Ear) _ _ ?_ (List.reverse_perm _).symm
        intro l u hl; refine congr_arg W.asks ?_; funext r; exact pair_perm _ line_sym (hl.append_right _)
      exact hP.trans (hg.symm.trans (showBlind hW L (convertWalk.mp h)))
    change Φ r = _
    exact (is_const_of_deriv_eq_zero (fun t=> (hz t).differentiableAt) (fun t=> (hz t).deriv) r 1).trans he

end YM.RG11.Rigidity
