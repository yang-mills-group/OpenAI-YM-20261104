import YM.Integration.UniformCoefficientEnvelope
import YM.RemainderComparison.CoefficientPrices.Anchors
import YM.RemainderComparison.Lacuna.Tall
import YM.RemainderComparison.Passion.Prisms

/-!
Uniform prices for the actual marked residual of a `Manor.Spinal` supplier.
The supremum over independent tests and fields is taken before summation.
The total bill depends on the number of marker labels, not the lattice volume.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.SpinalCoefficientPrice

open Function Finset Lattice Wilson RG Marker
open Push.AbsoluteSums
open RemainderComparison RemainderComparison.WickReps
open RemainderComparison.CoefficientPrices
open scoped Classical BigOperators

variable {G : Gauge} {c : Side} {ι θ I : Type} {α : Type*}
variable [DecidableEq θ] {J : Census θ}
variable (T : Manor G c ι α I) (P : BudgetPoint) (Z : Set ι)
variable (z : ι → Poly J)

/-- Precisely the marked part of the supplier, as used by `Lacuna.day`. -/
def active : Set I := (Lobby.night T Z)ᶜ

/-- A coefficient majorant formed from the actual controls and actual mask. -/
def coefficientCost (i : I) (q : J.Mode) : ℝ :=
  ‖(Mosaic.Verse.controls Z z (T.marks i)).part q‖ *
    maskedCost T (active T Z) P i

/-- Tests and fields have already been maximized inside each summand. -/
def coefficientBound (q : J.Mode) : ℝ := ∑' i, coefficientCost T P Z z i q

variable {T P Z z} {root : ι → Support c} {roots : θ → Site c}
variable {D : ι → Finset θ} {w : θ → ℝ} {σ μ : ℝ} {k : ℕ}

lemma coefficientCost_nonnegative (H : T.Spinal (active T Z) root P σ μ)
    (i : I) (q : J.Mode) : 0 ≤ coefficientCost T P Z z i q :=
  mul_nonneg (norm_nonneg _) ((spinal_masked_cost H).1 i)

lemma coefficientCost_quiet (hO : Passion.Oriented D J Z z) (i : I) :
    coefficientCost T P Z z i J.quiet = 0 := by
  by_cases hi : i ∈ active T Z
  · have hn : Mosaic.Verse.load Z (T.marks i) ≠ 0 := hi
    simp [coefficientCost, Passion.positive hO (T.marks i) hn]
  · simp [coefficientCost, maskedCost, hi]

/-- Nonzero coefficient costs retain every marked root. The zero-cost case
is essential: `Sees.travels` only constrains nonzero actual wet values. -/
lemma coefficientCost_follows (H : T.Spinal (active T Z) root P σ μ)
    (hO : Passion.Oriented D J Z z)
    (hroot : ∀ i t, t ∈ D i → roots t ∈ root i)
    (i : I) (q : J.Mode) (t : θ) (ht : t ∈ q.val)
    (hc : coefficientCost T P Z z i q ≠ 0) : roots t ∈ T.halls i := by
  have hpart : (Mosaic.Verse.controls Z z (T.marks i)).part q ≠ 0 := by
    intro hz
    apply hc
    simp [coefficientCost, hz]
  have hi : i ∈ active T Z := by
    by_contra hn
    apply hc
    simp [coefficientCost, maskedCost, hn]
  have hword := Passion.spark hO (T.marks i) q hpart
  obtain ⟨j, hj, htd⟩ := Multiset.mem_bind.mp
    (show t ∈ Solos.mapWord D (T.marks i) from hword ▸ ht)
  obtain ⟨f, hf, hF, hB⟩ := H.grants
  by_contra hnot
  have hzero (a : α) (U : Config G c) : T.wet P a i U = 0 := by
    by_contra hn
    exact hnot (((hF i hi).1.travels a) j hj U hn (hroot j t htd))
  have hcost : maskedCost T (active T Z) P i = 0 := by
    apply le_antisymm
    · rw [maskedCost, if_pos hi]
      exact envelope_le (by positivity) (fun v => by simp only [hzero, norm_zero, le_refl])
    · exact (spinal_masked_cost H).1 i
  exact hc (by simp [coefficientCost, hcost])

/-- The supplied Spinal bill pays the coefficient/root ancestry ledger. -/
theorem loan (H : T.Spinal (active T Z) root P σ μ)
    (hO : Passion.Oriented D J Z z) (hC : Serif.Chorus J w Z z k)
    (hroot : ∀ i t, t ∈ D i → roots t ∈ root i) :
    Loan J w roots T.halls P σ (coefficientCost T P Z z) μ := by
  have hh := spinal_masked_cost H
  apply occupied roots σ T.halls (coefficientCost T P Z z) hC.votes
    (coefficientCost_nonnegative H) (coefficientCost_follows H hO hroot)
  apply tallyI (maskedCost T (active T Z) P) σ hh.2.2
    (fun i q => Poly.toll w q * coefficientCost T P Z z i q)
  · intro i q
    exact mul_nonneg (Poly.worth hC.votes q).le (coefficientCost_nonnegative H i q)
  · intro i
    calc
      (∑ q : J.Mode, Poly.toll w q * coefficientCost T P Z z i q) =
          Poly.price w (Mosaic.Verse.controls Z z (T.marks i)) *
            maskedCost T (active T Z) P i := by
        simp only [coefficientCost, Poly.price, Finset.sum_mul, mul_assoc]
      _ ≤ 1 * maskedCost T (active T Z) P i :=
        mul_le_mul_of_nonneg_right (Serif.bought hC (T.marks i)) (hh.1 i)
      _ = maskedCost T (active T Z) P i := one_mul _

lemma nonquiet_has_label (q : J.Mode) (hq : q ≠ J.quiet) : q.val.Nonempty := by
  apply Finset.nonempty_iff_ne_empty.mpr
  intro he
  exact hq (Subtype.ext he)

/-- Every nonquiet mode has an actual marked root at which its bill is paid. -/
theorem coefficient_budget (H : T.Spinal (active T Z) root P σ μ)
    (hO : Passion.Oriented D J Z z) (hC : Serif.Chorus J w Z z k)
    (hroot : ∀ i t, t ∈ D i → roots t ∈ root i) (hσ : 0 ≤ σ)
    (q : J.Mode) :
    SumBudget (fun i => coefficientCost T P Z z i q)
      (if q = J.quiet then 0 else (Poly.toll w q)⁻¹ * μ) := by
  by_cases hq : q = J.quiet
  · subst q
    simp only [coefficientCost_quiet hO]
    exact ⟨fun _ => le_rfl, summable_zero, by simp⟩
  · rw [if_neg hq]
    obtain ⟨t, ht⟩ := nonquiet_has_label q hq
    have hb := Loan.specific roots σ T.halls (coefficientCost T P Z z)
      hC.votes (loan H hO hC hroot) q t ht
    apply budget_mono hb (coefficientCost_nonnegative H · q)
    intro i
    exact le_mul_of_one_le_left (coefficientCost_nonnegative H i q)
      (Real.one_le_exp (mul_nonneg hσ (Nat.cast_nonneg _)))

lemma coefficientBound_quiet (hO : Passion.Oriented D J Z z) :
    coefficientBound T P Z z J.quiet = 0 := by
  simp [coefficientBound, coefficientCost_quiet hO]

theorem coefficientBound_nonnegative (H : T.Spinal (active T Z) root P σ μ)
    (q : J.Mode) : 0 ≤ coefficientBound T P Z z q :=
  tsum_nonneg (coefficientCost_nonnegative H · q)

theorem coefficientBound_le (H : T.Spinal (active T Z) root P σ μ)
    (hO : Passion.Oriented D J Z z) (hC : Serif.Chorus J w Z z k)
    (hroot : ∀ i t, t ∈ D i → roots t ∈ root i) (hσ : 0 ≤ σ)
    (q : J.Mode) (hq : q ≠ J.quiet) :
    coefficientBound T P Z z q ≤ μ / Poly.toll w q := by
  have hb := (coefficient_budget H hO hC hroot hσ q).2.2
  simpa [coefficientBound, hq, div_eq_mul_inv, mul_comm] using hb

/-- Every coefficient of the literal residual is bounded uniformly over the
test choice and the full field space, with its original mask retained. -/
theorem day_part_le (H : T.Spinal (active T Z) root P σ μ)
    (hO : Passion.Oriented D J Z z) (hC : Serif.Chorus J w Z z k)
    (hroot : ∀ i t, t ∈ D i → roots t ∈ root i) (hσ : 0 ≤ σ)
    (a : α) (U : Config G c) (q : J.Mode) :
    ‖(Lacuna.day J Z T P z a U).part q‖ ≤ coefficientBound T P Z z q := by
  have hb := coefficient_budget H hO hC hroot hσ q
  have hs := hb.2.1.subtype (active T Z)
  have hp (i : active T Z) : ‖(T.paint P Z z a U i.val).part q‖ ≤
      coefficientCost T P Z z i.val q := by
    have hw := (spinal_masked_cost H).2.1 i.val i.prop a U
    simpa only [Manor.paint, Poly.part_smul, norm_mul, Complex.norm_real,
      coefficientCost, mul_comm] using
      mul_le_mul_of_nonneg_right hw (norm_nonneg ((Mosaic.Verse.controls Z z (T.marks i.val)).part q))
  have hn := hs.of_nonneg_of_le (fun i => norm_nonneg _) hp
  have hpaint := Manor.standing a U Z z H.templary hC hσ
  change ‖(∑' i : active T Z, T.paint P Z z a U i.val).part q‖ ≤ _
  rw [Poly.share hpaint]
  calc
    ‖∑' i : active T Z, (T.paint P Z z a U i.val).part q‖ ≤
        ∑' i : active T Z, ‖(T.paint P Z z a U i.val).part q‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' i : active T Z, coefficientCost T P Z z i.val q := hn.tsum_le_tsum hp hs
    _ ≤ ∑' i, coefficientCost T P Z z i q :=
      Summable.tsum_le_tsum_of_inj Subtype.val Subtype.val_injective
        (fun i _ => coefficientCost_nonnegative H i q) (fun _ => le_rfl) hs hb.2.1
    _ = coefficientBound T P Z z q := rfl

section FiniteMarkers
variable [Fintype θ]

/-- Sum the ancestry receipts over marker labels. A nonquiet mode is charged
at one of its labels, so the bill is linear in the marker count. -/
theorem total_budget (H : T.Spinal (active T Z) root P σ μ)
    (hO : Passion.Oriented D J Z z) (hC : Serif.Chorus J w Z z k)
    (hroot : ∀ i t, t ∈ D i → roots t ∈ root i) (hσ : 0 ≤ σ) :
    SumBudget (fun p : I × J.Mode => Poly.toll w p.2 *
      coefficientCost T P Z z p.1 p.2) (Fintype.card θ * μ) := by
  let g := coefficientCost T P Z z
  have hL := loan H hO hC hroot
  let f (t : θ) (p : I × J.Mode) :=
    if t ∈ p.2.val then Poly.toll w p.2 * g p.1 p.2 *
      Real.exp (σ * coverNumber P.B (T.halls p.1)) else 0
  have hf (t : θ) (p : I × J.Mode) : 0 ≤ f t p := (hL.ancestry t).1 p
  have hb := budget_over Finset.univ f (fun _ => μ) (fun t _ => hL.ancestry t)
  have hn (p : I × J.Mode) : 0 ≤ Poly.toll w p.2 * g p.1 p.2 :=
    mul_nonneg (Poly.worth hC.votes p.2).le (hL.nonnegative p.1 p.2)
  have hle (p : I × J.Mode) : Poly.toll w p.2 * g p.1 p.2 ≤ ∑ t : θ, f t p := by
    by_cases hq : p.2 = J.quiet
    · have hz : g p.1 p.2 = 0 := by simpa [hq, g] using coefficientCost_quiet hO p.1
      rw [hz, mul_zero]
      exact Finset.sum_nonneg (fun t _ => hf t p)
    · obtain ⟨t, ht⟩ := nonquiet_has_label p.2 hq
      calc
        Poly.toll w p.2 * g p.1 p.2 ≤
            Poly.toll w p.2 * g p.1 p.2 * Real.exp (σ * coverNumber P.B (T.halls p.1)) :=
          le_mul_of_one_le_right (hn p) (Real.one_le_exp (mul_nonneg hσ (Nat.cast_nonneg _)))
        _ = f t p := (if_pos ht).symm
        _ ≤ ∑ t : θ, f t p := Finset.single_le_sum (fun t _ => hf t p) (Finset.mem_univ t)
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using budget_mono hb hn hle

/-- The finite-marker price is uniform over independent tests and fields. -/
theorem coefficientBound_price (H : T.Spinal (active T Z) root P σ μ)
    (hO : Passion.Oriented D J Z z) (hC : Serif.Chorus J w Z z k)
    (hroot : ∀ i t, t ∈ D i → roots t ∈ root i) (hσ : 0 ≤ σ) :
    (∑ q : J.Mode, Poly.toll w q * coefficientBound T P Z z q) ≤
      Fintype.card θ * μ := by
  have hb := total_budget H hO hC hroot hσ
  calc
    (∑ q : J.Mode, Poly.toll w q * coefficientBound T P Z z q) =
        ∑ q : J.Mode, ∑' i, Poly.toll w q * coefficientCost T P Z z i q := by
      simp only [coefficientBound, tsum_mul_left]
    _ = ∑' q : J.Mode, ∑' i, Poly.toll w q * coefficientCost T P Z z i q :=
      (tsum_fintype _).symm
    _ = ∑' i, ∑' q : J.Mode, Poly.toll w q * coefficientCost T P Z z i q := hb.2.1.tsum_comm
    _ = ∑' p : I × J.Mode, Poly.toll w p.2 * coefficientCost T P Z z p.1 p.2 := hb.2.1.tsum_prod.symm
    _ ≤ Fintype.card θ * μ := hb.2.2

/-- The envelope remains inside the finite coefficient sum, so independent
test functions are uniformly controlled before the normalized comparison. -/
theorem day_envelope_price (H : T.Spinal (active T Z) root P σ μ)
    (hO : Passion.Oriented D J Z z) (hC : Serif.Chorus J w Z z k)
    (hroot : ∀ i t, t ∈ D i → roots t ∈ root i) (hσ : 0 ≤ σ) :
    (∑ q : J.Mode, Poly.toll w q * envelope
      (fun v : α × Config G c => ‖(Lacuna.day J Z T P z v.1 v.2).part q‖)) ≤
        Fintype.card θ * μ := by
  apply le_trans _ (coefficientBound_price H hO hC hroot hσ)
  apply Finset.sum_le_sum
  intro q _
  apply mul_le_mul_of_nonneg_left _ (Poly.worth hC.votes q).le
  exact envelope_le (coefficientBound_nonnegative H q)
    (fun v => day_part_le H hO hC hroot hσ v.1 v.2 q)

end FiniteMarkers

section CanonicalMarkers
variable {V : Type} [DecidableEq V] (Jv : Census V)

/-- The actual unit marker for each independent test-function occurrence. -/
def canonicalMarkers (i : V) : Poly Jv := Poly.send (Jv.fire i) 1

theorem canonical_oriented :
    Passion.Oriented (fun i : V => {i}) Jv Set.univ (canonicalMarkers Jv) := by
  refine ⟨⟨fun i => by simp⟩, ?_⟩
  intro i _ q hq
  rw [canonicalMarkers, Poly.part_send, if_neg]
  intro he
  exact hq (congrArg Subtype.val he)

theorem canonical_square (i : V) : canonicalMarkers Jv i * canonicalMarkers Jv i = 0 := by
  ext q
  change (Poly.prod (Poly.send (Jv.fire i) 1) (Poly.send (Jv.fire i) 1)).part q = 0
  rw [Poly.cart]
  simp [Poly.merges, Census.fire]

theorem canonical_chorus_of_capacity {v : V → ℝ} {k : ℕ}
    (hv : ∀ i, 0 < v i) (hle : ∀ i, v i ≤ 1)
    (hcap : ∀ q : Jv.Mode, q.val.card ≤ k) :
    Serif.Chorus Jv v Set.univ (canonicalMarkers Jv) k := by
  apply Serif.production (canonicalMarkers Jv) v Set.univ hv (canonical_square Jv)
  · intro i _
    constructor
    · simpa [canonicalMarkers] using hle i
    · simp [canonicalMarkers, Ne.symm (Jv.fire_hot i)]
  · exact hcap

theorem canonical_chorus [Fintype V] {v : V → ℝ}
    (hv : ∀ i, 0 < v i) (hle : ∀ i, v i ≤ 1) :
    Serif.Chorus Jv v Set.univ (canonicalMarkers Jv) (Fintype.card V) :=
  canonical_chorus_of_capacity Jv hv hle (fun q => Finset.card_le_univ q.val)

/-- In the unit-marker application the orientation and price suppliers are
proved here. Only the original Spinal estimate and actual support roots remain. -/
theorem canonical_day_envelope_price [Fintype V]
    {T : Manor G c V α I} {P : BudgetPoint} {root : V → Support c}
    {roots : V → Site c} {v : V → ℝ} {σ μ : ℝ}
    (H : T.Spinal (active T Set.univ) root P σ μ)
    (hv : ∀ i, 0 < v i) (hle : ∀ i, v i ≤ 1)
    (hroot : ∀ i, roots i ∈ root i) (hσ : 0 ≤ σ) :
    (∑ q : Jv.Mode, Poly.toll v q * envelope
      (fun a : α × Config G c =>
        ‖(Lacuna.day Jv Set.univ T P (canonicalMarkers Jv) a.1 a.2).part q‖)) ≤
      Fintype.card V * μ := by
  apply day_envelope_price (roots := roots) H (canonical_oriented Jv) (canonical_chorus Jv hv hle) _ hσ
  intro i t ht
  have he : t = i := Finset.mem_singleton.mp ht
  subst t
  exact hroot i

end CanonicalMarkers

end YM.Integration.SpinalCoefficientPrice
