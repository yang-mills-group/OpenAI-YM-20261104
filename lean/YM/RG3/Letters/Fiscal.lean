import YM.RG3.Letters.Skeleton
import YM.Push.ABSOLUTE_SUMS.Basic

/-! Positive account for the same complete selections used by `Frame.after`.

Pump *hard* letters by `χ` (≥1) ; every patch pays once (or more), including
the patches only carrying a single unchanged old letter. This suffices without
any Δ-degree or marker-count factor, even before restoring a polynomial
choice, hence we insist on the hit (not merely root-marker) test on the
inputs to this operation. See also alternatives in `Distinct` for rooted
estimates. The one full cover exponent and the volume of a B-cover in
`forest` must be inserted in the RG ledger, also if using fixed marker load.
No growth with the torus volume, number of addresses, or tag count *past the
visible hypotheses*. No automatic purchase across a step or calendar.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Letters.Frame
open RG Ac Lattice Push.AbsoluteSums Finset

variable {n : Side} {ι : Type*} [DecidableEq ι] (D : Frame n ι)

open scoped Classical in
def pump (f : ι → ℝ) (χ : ℝ) (i : ι) := if D.Hard i then χ*f i else f i

def charge (f : ι → ℝ) (c : D.Patch) := ∏ i∈D.letters c, f i

variable (M : ℕ) (a γ χ : ℝ) (f : ι → ℝ) (hf : ∀ i,0 ≤ f i)

omit [DecidableEq ι] in
include hf in
theorem charge_nonneg (p : D.Patch) : 0 ≤ D.charge f p := Finset.prod_nonneg fun i _ => hf i

include hf in
theorem pump_prod (hχ : 1 ≤ χ) (p : D.Patch) :
    χ*D.charge f p ≤ D.charge (D.pump f χ) p := by
  classical
  obtain ⟨i, hi', h⟩ := p.property.2.1
  have hi : i∈D.letters p := hi'
  unfold charge
  rw [← Finset.mul_prod_erase _ f hi, ← Finset.mul_prod_erase _ (D.pump f χ) hi,
    show D.pump f χ i = χ*f i from if_pos h, ← mul_assoc]
  refine mul_le_mul_of_nonneg_left (prod_le_prod (fun j _ => hf j) (fun j _ => ?_))
    (mul_nonneg (zero_le_one.trans hχ) (hf i))
  unfold pump
  split
  · exact le_mul_of_one_le_left (hf j) hχ
  exact le_rfl

include hf in
/-- Direct support price for the new alphabet of *distinct letter* patches,
full union at the declared cover exponent. `g` can later be the poly cost
from genuine coefficientwise envelopes. -/
theorem pumped (hχ : 1 ≤ χ) (ha : 0≤a) (hγ : 0≤γ)
    (hH : Hit D.read M (D.pump f χ) (a+1) γ) (green : (M+M+1:ℕ)^4*(γ:ℝ) ≤ 1)
    (g : D.Patch → ℝ) (hg : ∀ i, 0≤g i) (covered : ∀ i, g i ≤ D.charge f i) :
    Hit D.ground M g a ((Real.exp γ-1)/χ) := by
  intro x
  have hχ' : 0 < χ := zero_lt_one.trans_le hχ
  rw [div_eq_inv_mul]
  have he := budget_pull D.letters D.letters_injective
    (budget_scale (x:=χ⁻¹) (by positivity) (forest D.read M ha
      (fun i => show 0 ≤ D.pump f χ i from by
        unfold pump
        split
        · exact mul_nonneg hχ'.le (hf i)
        · exact hf i)
      hH green hγ x))
  refine budget_mono he (fun i => ?_) (fun i => ?_)
  · split
    · exact mul_nonneg (hg i) (Real.exp_pos _).le
    exact le_rfl
  split
  next ht =>
    rw [roots,if_pos (show Spark D.read (D.letters i) ∧ x∈(D.letters i).biUnion D.read from ⟨i.property.1,ht⟩),inv_mul_eq_div,le_div_iff₀ hχ']
    calc
      _ = Real.exp (a*coverNumber M (D.ground i)) * (χ*g i) := by ring
      _ ≤ Real.exp (a*coverNumber M (D.ground i)) * D.charge (D.pump f χ) i :=
        mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left (covered i) hχ'.le).trans
          (D.pump_prod χ f hf hχ i)) (Real.exp_pos _).le
  exact he.1 i

-- Qualitative summability follows already from the input hit at this fixed
-- torus, without `green`. Track any use of the extensive cost separately.
omit [DecidableEq ι] in
theorem from_hit {X : ι → Support n} (hx : ∀ i,(X i).Nonempty) (hf : ∀ i,0 ≤ f i) (ha : 0≤a)
    (hH : Hit X M f a γ) :
    SumBudget f (Fintype.card (Site n) * γ) := by
  classical
  let b (x : Site n) i := if x∈ X i then f i * Real.exp (a*coverNumber M (X i)) else 0
  have heq : ∑ _ : Site n, γ = Fintype.card (Site n)*γ := by simp
  rw [← heq]
  have he := budget_over univ b (fun _ => γ) (fun i _ => hH i)
  refine budget_mono he hf (fun i => ?_)
  obtain ⟨x,hx'⟩ := hx i
  apply le_trans _ (single_le_sum (f:=fun j => b j i) (fun j _ => (hH j).1 i) (mem_univ x))
  dsimp only [b]; rw [if_pos hx']
  exact le_mul_of_one_le_right (hf _) (Real.one_le_exp (mul_nonneg ha (Nat.cast_nonneg _)))

end YM.RG3.Letters.Frame
