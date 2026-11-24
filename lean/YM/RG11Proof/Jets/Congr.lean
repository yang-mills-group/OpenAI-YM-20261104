import YM.PertExtension.PositionNetwork

/-!
# Finite reporting jets

Ordinary power series coefficients through an **inclusive** horizon in the
power. The submitted comparison is to be all fixed finite orders, not
convergence. Keeping this relation exposed helps not silently use an order n+1
premise after differentiation or composition. `FrameAt` and `Mark` (arity per
profile) and `insert` here are those of YM.PertExtension.Position, with rows
input labels (transform applies in all slots of the full correlations). Nothing
in this file says what coefficients either side actually has.
-/

set_option autoImplicit false
noncomputable section

namespace YM.RG11.Jets
open PowerSeries YM.PertExtension.Position
open scoped BigOperators Classical

variable {R S : Type*}

/-- Inclusive truncated equality in the **coefficient**, no norm implicit.
Indices outside `[0,n]` are entirely unconstrained. -/
def Through [Semiring R] (n : ℕ) (p q : PowerSeries R) : Prop :=
  ∀ i ≤ n, coeff i p = coeff i q

namespace Through

section
variable [Semiring R] {p q r s : R⟦X⟧} {m n : ℕ}

@[refl] theorem refl (p : R⟦X⟧) : Through n p p := fun _ _ => rfl
@[symm] theorem symm (h : Through n p q) : Through n q p := fun i hi => (h i hi).symm
theorem trans (h : Through n p q) (k : Through n q r) : Through n p r :=
  fun i hi => (h i hi).trans (k i hi)

theorem of_le (hp : m ≤ n) (h : Through n p q) : Through m p q :=
  fun i hi => h i (hi.trans hp)
theorem head (h : Through n p q) : constantCoeff p = constantCoeff q := by
  simp only [← coeff_zero_eq_constantCoeff_apply]; exact h 0 (Nat.zero_le n)

theorem add (h : Through n p q) (k : Through n r s) : Through n (p+r) (q+s) := by
  intro i hi
  simp only [map_add,h i hi,k i hi]

theorem mul (h : Through n p q) (k : Through n r s) : Through n (p*r) (q*s) := by
  intro i hi
  simp only [coeff_mul]
  refine Finset.sum_congr rfl ?_
  rintro ⟨a,b⟩ ht
  have ht := Finset.HasAntidiagonal.mem_antidiagonal.mp ht
  dsimp at ht ⊢
  rw [h _ (by omega), k _ (by omega)]

theorem pow (h : Through n p q) (l : ℕ) : Through n (p^l) (q^l) := by
  induction l with
  | zero => simp only [pow_zero]; exact refl _
  | succ l H => simpa only [pow_succ] using H.mul h

theorem sum {I : Type*} {u : Finset I} {f g : I → R⟦X⟧} (H : ∀ i ∈ u, Through n (f i) (g i)) :
    Through n (∑ i ∈ u, f i) (∑ i ∈ u, g i) := by
  intro j hj
  rw [map_sum,map_sum]
  exact Finset.sum_congr rfl (fun i hi => H i hi j hj)
end

section
variable [Ring R] {p q r s : R⟦X⟧} {n : ℕ}
theorem neg (h : Through n p q) : Through n (-p) (-q) := by
  intro i hi; simp [h i hi]
theorem sub (h : Through n p q) (k : Through n r s) : Through n (p-r) (q-s) := by
  simp_rw [sub_eq_add_neg]; exact h.add k.neg
end

section
variable [CommSemiring R] {p q : R⟦X⟧} {n : ℕ}
theorem prod {I : Type*} {u : Finset I} {f g : I → R⟦X⟧} (H : ∀ i∈u, Through n (f i) (g i)) :
    Through n (∏ i∈u, f i) (∏ i∈u, g i) := by
  classical
  induction u using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; exact refl _
  | insert j s hj hs =>
    simp only [Finset.prod_insert hj]
    exact (H j (by simp)).mul (hs (fun i hi => H i (by simp [hi])))

-- order-by-order insert coherence on **this** finite field space. See
-- `RG11.doc` for the different restriction problem in *field horizon*.
theorem slots {J P : Type*} [Fintype J] {arity : P → ℕ} {v : Mark J arity}
    {A B : Mark J arity → R⟦X⟧} {K H : FrameAt J R⟦X⟧}
    (hab : ∀ w, Through n (A ⟨v.1,w⟩) (B ⟨v.1,w⟩))
    (hKH : ∀ i j, Through n (K (v.2 i) j) (H (v.2 i) j)) :
    Through n (PertExtension.Position.insert J arity A K v)
      (PertExtension.Position.insert J arity B H v) :=
  sum fun w _ => (hab w).mul (prod (fun i _ => hKH i _))
end

section
variable [Field R] {p q : R⟦X⟧} {m n : ℕ}
/-- Includes degenerate constant cases (mathlib FPS inverse convention). For
an actual inverse change one must ALSO prove the unit-leading hypothesis. -/
theorem inv (h : Through n p q) : Through n p⁻¹ q⁻¹ := by
  intro i hi
  by_cases hz : constantCoeff p=0
  · have hw := h.head.symm.trans hz
    -- see PowerSeries.coeff_inv
    rw [PowerSeries.coeff_inv,PowerSeries.coeff_inv]
    simp [hz,hw]
  induction i using Nat.strong_induction_on with
  | h i ih =>
    rw [PowerSeries.coeff_inv, PowerSeries.coeff_inv,h.head]
    congr 2
    refine Finset.sum_congr rfl ?_
    rintro ⟨a,b⟩ hb
    have ht := Finset.HasAntidiagonal.mem_antidiagonal.mp hb
    dsimp at ht ⊢
    split
    · rename_i hx
      rw [h a (by omega), ih b hx (by omega)]
    rfl
end
end Through

/-- Prefix FPS with all higher coefficients zero. -/
def keep [Semiring R] (n : ℕ) (p : R⟦X⟧) : R⟦X⟧ :=
  mk fun i => if i ≤ n then coeff i p else 0

@[simp] theorem coeff_keep [Semiring R] (i n) (p : R⟦X⟧) :
    coeff i (keep n p) = if i ≤ n then coeff i p else 0 := by simp [keep]

theorem keep_through [Semiring R] (n) (p : R⟦X⟧) : Through n (keep n p) p :=
  fun _ hi => by simp [hi]
theorem keep_eq_iff [Semiring R] {n} {p q : R⟦X⟧} : keep n p = keep n q ↔ Through n p q := by
  constructor
  · intro e; have h := (keep_through n p).symm; rw [e] at h; exact h.trans (keep_through n q)
  intro e; ext i; by_cases h:i≤n <;> simp [h, fun hh=>e i hh]

end YM.RG11.Jets
