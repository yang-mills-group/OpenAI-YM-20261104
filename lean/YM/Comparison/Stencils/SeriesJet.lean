import YM.Comparison.Stencils.SlotCount
import YM.Next.RANK.ScaleScale

/-!
# Coupling part of the normalized projection, before basis coordinates

Exact rescaling of the normalized jet. We can execute on any finite-order data;
no denominator or pole in the output, even for unaffiliated finite-support
polynomial kernels. `stage e` reads only orders up through `e`. Tracks all
engineering components (not only the terminal one). Use separate
multiplication by address weights and separate choices of field horizon to
read jointly with test profiles.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.Stencils.Feed
open CubicMatch Lattice Function RG Wilson Symbols Labels Source Source.Drops Filter
open Next.Rank.LiftMark (factors weighed factors_C factors_X)
open Next.Foundations
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators
variable {G : Gauge} {S : Finset Cover} {σ : Type*}

abbrev LogSeries (G : Gauge) (S : Finset Cover) := ℕ → LocalPol G S

/-- One convolution diagonal entry (= orders added after the rescaling
of input and output letters). -/
def booth (H : Hol G) (d i : ℕ) : LocalPol G S →ₗ[ℂ] Pol G :=
  ∑ k ∈ Finset.range (d+1), portion (k+i) ∘ₗ projector H d ∘ₗ portion k

lemma booth_cap (H : Hol G) (d i : ℕ) (p : LocalPol G S) : booth H d i p ∈ limited G d := by
  unfold booth; rw [LinearMap.sum_apply]
  apply Submodule.sum_mem
  intro k _
  change portion _ (rawPi H d _) ∈ _
  unfold rawPi
  rw [← cap_portion]
  apply cap_limited

lemma booth_far (H : Hol G) (d i : ℕ) (p : LocalPol G S) (hi : d < i) : booth H d i p = 0 := by
  unfold booth; rw [LinearMap.sum_apply]
  apply Finset.sum_eq_zero
  intro k _
  exact slots_past (rawPi H d (portion k p)) (raw_cap H d _) (lt_of_lt_of_le hi (Nat.le_add_left _ _))

lemma booth_one (H : Hol G) (d i : ℕ) {p : LocalPol G S} {k : ℕ} (hp : Rank p k) :
    booth H d i p = portion (k+i) (projector H d p) := by
  unfold booth; rw [LinearMap.sum_apply]
  simp only [LinearMap.comp_apply]
  by_cases h : k ≤ d
  · rw [Finset.sum_eq_single_of_mem k (Finset.mem_range.mpr (Nat.lt_succ_of_le h)),
      on_rank p k hp k, if_pos rfl]
    intro m _ H'; rw [on_rank p k hp m, if_neg H', map_zero, map_zero]
  rw [projection_zero H d hp (Nat.lt_of_not_ge h), map_zero]; apply Finset.sum_eq_zero
  intro m hm; have hh := Finset.mem_range.mp hm
  rw [on_rank p k hp m, if_neg (by omega), map_zero, map_zero]

/-- Finite operation for any requested order. Lands in ambient radial label
polynomials (retain gauge-variant channels; use invariantSector separately). -/
def stage (H : Hol G) (d j : ℕ) : LogSeries G S →ₗ[ℂ] Pol G :=
  ∑ i ∈ Finset.range (j+1), booth H d (j-i) ∘ₗ LinearMap.proj i

lemma stage_at (H : Hol G) (d j : ℕ) (P : LogSeries G S) :
    stage H d j P = ∑ i ∈ Finset.range (j+1), booth H d (j-i) (P i) := by
  unfold stage
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]

lemma stage_cap (H : Hol G) (d j : ℕ) (P : LogSeries G S) : stage H d j P ∈ limited G d := by
  rw [stage_at]
  exact Submodule.sum_mem _ fun i _ => booth_cap ..

/-- Order truncation doesn't affect the retained calculation. -/
theorem stage_truncated (H : Hol G) (d j : ℕ) {P Q : LogSeries G S}
    (h : ∀ i ≤ j, P i = Q i) : stage H d j P = stage H d j Q := by
  rw [stage_at, stage_at]
  exact Finset.sum_congr rfl fun i hi => congrArg _ (h i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))

lemma onePulse (H : Hol G) (d j i : ℕ) (p : LocalPol G S) :
    stage H d j (Pi.single i p) = if i ≤ j then booth H d (j-i) p else 0 := by
  rw [stage_at]
  by_cases h : i ≤ j
  · rw [if_pos h, Finset.sum_eq_single_of_mem i (Finset.mem_range.mpr (Nat.lt_succ_of_le h)),
      Pi.single_eq_same]
    intro b _ hb; rw [Pi.single_eq_of_ne hb, map_zero]
  rw [if_neg h]; refine Finset.sum_eq_zero fun b hb => ?_
  have he := Finset.mem_range.mp hb
  rw [Pi.single_eq_of_ne (by omega), map_zero]

/-- Numeric finite-order evaluation for checking degree books. -/
def priced (g : ℂ) (r : ℕ) (P : ℕ → MvPolynomial σ ℂ) :=
  ∑ i ∈ Finset.range (r+1), g^i • P i

def cutLog (P : LogSeries G S) (r : ℕ) :=
  ∑ i ∈ Finset.range (r+1), Pi.single i (P i)

lemma cut_in (P : LogSeries G S) {i r : ℕ} (h : i ≤ r) : cutLog P r i = P i := by
  rw [cutLog, Finset.sum_apply, Finset.sum_eq_single_of_mem i
    (Finset.mem_range.mpr (Nat.lt_succ_of_le h))]
  · rw [Pi.single_eq_same]
  intro b _ hb
  rw [Pi.single_eq_of_ne hb.symm]

lemma coat_rank (g : ℂ) (p : MvPolynomial σ ℂ) {k : ℕ} (hp : Rank p k) :
    factors g p = g^k • p := by
  ext i
  rw [Next.Rank.LiftMark.factors, Next.Rank.Perch.jets_coeff, MvPolynomial.coeff_smul]
  by_cases h : p.coeff i = 0
  · rw [h, mul_zero, smul_zero]
  rw [hp h]; rfl

lemma coats_input (g : ℝ) (P : LocalPol G S) (v) :
    inscribe v (factors (g : ℂ) P) = inscribe (g • v) P := by
  induction P using MvPolynomial.induction_on with
  | C x => simp [inscribe]
  | add p q hp hq => simp only [map_add,hp,hq]
  | mul_X p k hp => rw [map_mul, map_mul, map_mul, hp, factors_X]; simp [inscribe]

lemma coats_output {d : ℕ} (F : Frame G d) (v : F.Coeff) (g : ℝ) :
    factors (g : ℂ) (F.coords.symm v).val = (F.coords.symm (F.scaled g v)).val :=
  (weighed F v g).symm

lemma overfull (H : Hol G) (d : ℕ) (P : LocalPol G S) {k : ℕ} (h : Rank P k) :
    projector H d P = ∑ i ∈ Finset.range (d+1), booth H d i P := by
  simp_rw [booth_one H d _ h]
  let f (i : ℕ) := portion i (projector H d P)
  have he : ∑ i ∈ Finset.range k, f i = 0 := Finset.sum_eq_zero fun i hi =>
    projection_rank H d h (Finset.mem_range.mp hi)
  calc
    _ = ∑ i ∈ Finset.range (d+1), f i := (slots_full (projector H d P) (raw_cap ..)).symm
    _ = ∑ i ∈ Finset.range (d+1+k), f i := Finset.sum_subset (Finset.range_mono (by omega))
      (fun j _ hj => slots_past (projector H d P) (raw_cap ..) (show d < j from by
        simp only [Finset.mem_range, Nat.not_lt] at hj; omega))
    _ = _ := by rw [add_comm (d+1) k, Finset.sum_range_add, he, zero_add]

lemma toll_one (H : Hol G) (d : ℕ) (g : ℂ) (hg : g ≠ 0) {P : LocalPol G S} {k : ℕ}
    (h : Rank P k) :
    factors g (projector H d (factors g⁻¹ P)) = priced g d (fun i => booth H d i P) := by
  rw [coat_rank g⁻¹ P h, map_smul, map_smul, overfull H d P h, map_sum, priced, Finset.smul_sum]
  apply Finset.sum_congr rfl; intro i _
  have hx : Rank (booth H d i P) (k+i) := by
    rw [booth_one H d i h]
    apply portion_in
  rw [coat_rank g _ hx, smul_smul, pow_add, ← mul_assoc, inv_pow, inv_mul_cancel₀ (pow_ne_zero k hg), one_mul]

lemma toll_pol (H : Hol G) (d : ℕ) (g : ℂ) (hg : g ≠ 0) (P : LocalPol G S) :
    factors g (projector H d (factors g⁻¹ P)) = priced g d (fun i => booth H d i P) := by
  induction P using MvPolynomial.induction_on' with
  | monomial v c =>
    exact toll_one H d g hg
      (MvPolynomial.isWeightedHomogeneous_monomial (fun _ => 1) v c rfl)
  | add P Q hP hQ => simp only [map_add, smul_add, hP, hQ, priced, Finset.sum_add_distrib]

lemma priced_pulse (H : Hol G) (g : ℂ) (d i : ℕ) (r : ℕ) (hi : i ≤ r) (P : LocalPol G S) :
    priced g (r+d) (fun t => stage H d t (Pi.single i P)) =
      g^i • priced g d (fun j => booth H d j P) := by
  let F (j : ℕ) := g^j • stage H d j (Pi.single i P)
  have he : ∑ j ∈ Finset.range i, F j = 0 := Finset.sum_eq_zero fun j hj => by
    dsimp only [F]; rw [onePulse, if_neg (not_le_of_gt (Finset.mem_range.mp hj)), smul_zero]
  unfold priced
  rw [Finset.smul_sum]
  change ∑ j ∈ Finset.range (r+d+1), F j = _
  calc
    _ = ∑ j ∈ Finset.range (i+(d+1)), F j := (Finset.sum_subset (Finset.range_mono (by omega))
      (fun j _ hj => by
        simp only [Finset.mem_range, Nat.not_lt] at hj
        dsimp only [F]; rw [onePulse, if_pos (by omega), booth_far H _ _ _ (by omega), smul_zero])).symm
    _ = _ := by
      rw [Finset.sum_range_add, he, zero_add]
      exact Finset.sum_congr rfl fun j _ => by simp [F, onePulse, pow_add, smul_smul]

/-- Check at every nonzero g (exact polynomial re-expression of the finite
calculation). Uses the indicated truncation on the RHS, no infinite sum. -/
theorem unscaled_check (H : Hol G) (d : ℕ) (P : LogSeries G S) (g : ℂ) (hg : g ≠ 0) (r : ℕ) :
    factors g (projector H d (factors g⁻¹ (priced g r P))) =
      priced g (r+d) (fun i => stage H d i (cutLog P r)) := by
  unfold priced cutLog
  simp only [map_sum, map_smul, Finset.smul_sum]
  rw [Finset.sum_comm (s := Finset.range (r+d+1))]
  exact Finset.sum_congr rfl fun t ht => by
    change g^t • _ = priced g (r+d) (fun j => stage H d j (Pi.single t (P t)))
    rw [priced_pulse H g d t r (Nat.le_of_lt_succ (Finset.mem_range.mp ht)), toll_pol H d g hg]
end YM.Comparison.Stencils.Feed
