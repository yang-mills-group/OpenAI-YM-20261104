import YM.FVA2.Wick.NoGhost
/-!
# Wick expectation identities in the super ring

The cap is only on rank, not a bottom valuation. Require the appropriate finite rank
hypotheses on each relevant coefficient. This lets us recognize Wick functionals by IBP.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Wick
open Function Set Finset Lattice Matrix
open MS MS.Plane MS.Koszul MS.Cylinder Taylor MS.Book MS.Orbit Cog MS.Swirl
open scoped BigOperators Topology ContDiff Matrix
variable {A : Type} [Fintype A]
local notation "T" => Raw A ℂ
variable {k:ℕ} {m : ℤ} {t : Raw A ℂ}

omit [Fintype A] in
lemma sym_mask {p : Sector A} (ht : Symm p t)(n : ℤ) : Symm p (mask n t) := by
  intro l i j r; unfold mask; by_cases h : ((l++i::j::r).length:ℤ)=n <;>
    simp [show (l++j::i::r).length=(l++i::j::r).length from by simp,
      ht l i j, List.length_append,List.length_cons] at * -- inspect

omit [Fintype A] in
lemma of_mask (H : Limit t k) : t = ∑ i∈Finset.Iic k, mask i t := by
  funext l; rw [Finset.sum_apply]; by_cases hl:l.length≤k
  · rw [Finset.sum_eq_single_of_mem l.length (Finset.mem_Iic.mpr hl)]
    · rw [enough (h:=(l.length:ℤ)) l rfl]
    exact fun i _ hi => strange l (by omega)
  rw [H l (by omega)]; exact (Finset.sum_eq_zero fun i hi => strange l (by obtain he:=Finset.mem_Iic.mp hi; omega)).symm

omit [Fintype A] in
lemma rankD (H : Book.rank m t) (i : A) : Book.rank (m-1) (D i t) := fun l hl => H (i::l) (by rw [mod_int] at hl ⊢; simp only [List.length_cons,Nat.cast_succ]; omega)
lemma letter_rank (p : Sector A) (H : Symm p t) (h : Book.rank k t) (hp : 0<k) :
    t = (k:ℂ)⁻¹ • ∑ i:A, product p (atLetter i) (D i t) := by
  have he : Tick (fun _:A=>1) t=(k:ℂ) • t := by
    funext l; change Owed (fun _:A=>1) l*t l=(k:ℂ)*t l
    by_cases hL:l.length=k
    · simp [Owed,hL]
    rw [h l (by rw [mod_int]; omega),mul_zero,mul_zero]
  rw [overture (fun _:A=>1) H] at he; simp_rw [one_smul] at he
  rw [he,inv_smul_smul₀ (show (k:ℂ)≠0 from (Nat.cast_ne_zero.mpr (by omega)))]

variable (p : Sector A) (K : Grain A) (he : Clear p K) (hs : Cog.Sym p K)
local infix:70 " ⋆ " => product p

include he hs
lemma view_unique (V:T→ₗ[ℂ]ℂ) (hv : ∀ i (F:T), Symm p F→ F ∈ Mini A →
    V (atLetter i ⋆ F)=∑ j, Chill K i j * V (D j F)) (h0 : ∀ z, V (coin z)=z)
    (F:T) (hF:Symm p F) (h:F∈ Mini A) : View K F=V F := by
  have h (t:T) (n:ℕ) (ht:Symm p t)(hl : Book.rank n t) : View K t= V t := by
    induction n using Nat.strong_induction_on generalizing t with
    | h n ih =>
        rcases n with _|n
        · rw [show t=coin (t []) from funext (fun l=>by cases l; exact rfl; exact hl _ (by rw [mod_int]; simp; omega))]; rw [minView,h0]
        have hk (v : A) : Book.rank n (D v t):= by convert! rankD hl v using 1; omega
        have hw (i j:A) : View K (D j (D i t))= V (D j (D i t)) := by
          by_cases hp:n=0; · subst n; rw [show D j (D i t)=0 from funext (fun l=> hk i _ (by rw [mod_int]; simp; omega)),map_zero,map_zero]
          exact ih (n-1) (by omega) (D j (D i t)) ((ht.drop i).drop j) (by convert! rankD (hk i) j using 1; omega)
        rw [letter_rank p ht hl (Nat.zero_lt_succ _)]
        simp_rw [map_smul,map_sum]; congr 1; refine Finset.sum_congr rfl fun i _ => ?_
        rw [ibpV i he hs (ht.drop i) (rankM (hk i)), hv i (D i t) (ht.drop i) (rankM (hk i))]; simp_rw [hw]
  rename_i Hm; obtain ⟨k,hk⟩ := Hm; rw [of_mask hk,map_sum,map_sum]
  exact Finset.sum_congr rfl fun i _ => h (mask i F) i (sym_mask hF _) (rankMod _ _)
end YM.FVA2.Wick
