import YM.Integration.SelectedPlanTriangular
import YM.Push.STATIONARY_UNIFORM.Calculus

/-! A finite coefficient bound for the exact auxiliary prior modifier.
The constants are finite sums of derivatives of fixed scalar functions at zero.
They precede every Plan, level, period and coefficient. Only a local smooth germ
is used; no predicted-beta positivity or actual-coupling hypothesis is needed. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.SelectedPlanPriorJetBound
open Function Finset IterationFour.Vacuum Push.Uniform
open Comparison.RG02.Assembly
open scoped ContDiff BigOperators Classical

def modifier (q : ℕ) (t : ℝ) : ℝ :=
  (1 + t) * ((Real.sqrt (1 + t))⁻¹) ^ q

def derivativeBudget (r : ℕ) (f : ℕ → ℝ → ℝ) : ℝ :=
  1 + ∑ k ∈ Finset.range (r + 3), ∑ j ∈ Finset.range (r + 5),
    ‖iteratedFDeriv ℝ j (f k) 0‖

def monomialBudget (r : ℕ) : ℝ :=
  derivativeBudget r (fun k (t : ℝ) => t ^ k)

def modifierBudget (r : ℕ) : ℝ := derivativeBudget r modifier

def indices (r e : ℕ) : Finset ℕ :=
  (Finset.range (r - 2 + 1)).filter (fun j => j < e)

def polynomial (r e : ℕ) (c : ℕ → ℝ) (g : ℝ) : ℝ :=
  ∑ j ∈ indices r e, c j * g ^ j

def mass (r e : ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ j ∈ indices r e, |c j|

def constant (r : ℕ) : ℝ :=
  ((r + 4).factorial : ℝ) * modifierBudget r * monomialBudget r ^ (r + 4)

private theorem budget_one (r : ℕ) (f : ℕ → ℝ → ℝ) :
    1 ≤ derivativeBudget r f := by
  unfold derivativeBudget
  have h : 0 ≤ ∑ k ∈ Finset.range (r + 3), ∑ j ∈ Finset.range (r + 5),
      ‖iteratedFDeriv ℝ j (f k) 0‖ :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  linarith

private theorem derivative_le (r : ℕ) (f : ℕ → ℝ → ℝ)
    (k j : ℕ) (hk : k ≤ r + 2) (hj : j ≤ r + 4) :
    ‖iteratedFDeriv ℝ j (f k) 0‖ ≤ derivativeBudget r f := by
  have h₁ : ‖iteratedFDeriv ℝ j (f k) 0‖ ≤
      ∑ t ∈ Finset.range (r + 5), ‖iteratedFDeriv ℝ t (f k) 0‖ :=
    Finset.single_le_sum (fun t _ => norm_nonneg (iteratedFDeriv ℝ t (f k) 0))
      (Finset.mem_range.mpr (by omega : j < r + 5))
  have h₂ : (∑ t ∈ Finset.range (r + 5), ‖iteratedFDeriv ℝ t (f k) 0‖) ≤
      ∑ a ∈ Finset.range (r + 3), ∑ t ∈ Finset.range (r + 5),
        ‖iteratedFDeriv ℝ t (f a) 0‖ :=
    Finset.single_le_sum
      (fun a _ => Finset.sum_nonneg fun t _ => norm_nonneg (iteratedFDeriv ℝ t (f a) 0))
      (Finset.mem_range.mpr (by omega : k < r + 3))
  unfold derivativeBudget
  linarith

private theorem modifier_smooth (q : ℕ) :
    ContDiffAt ℝ ω (modifier q) 0 := by
  have h : ContDiffAt ℝ ω (fun t : ℝ => 1 + t) 0 :=
    contDiffAt_const.add contDiffAt_id
  exact h.mul (((h.sqrt (by norm_num)).inv (by norm_num)).pow q)

private theorem monomial_allows (r k : ℕ) (hk : k ≤ r + 2) :
    Allows (r + 4) (fun t : ℝ => t ^ k) 0 (monomialBudget r) :=
  ⟨contDiffAt_id.pow k, fun j hj => derivative_le r (fun a (t : ℝ) => t ^ a) k j hk hj⟩

private theorem modifier_allows (r q : ℕ) (hq : q ≤ r + 2) :
    Allows (r + 4) (modifier q) 0 (modifierBudget r) :=
  ⟨modifier_smooth q, fun j hj => derivative_le r modifier q j hq hj⟩

private theorem mass_nonneg (r e : ℕ) (c : ℕ → ℝ) :
    0 ≤ mass r e c := Finset.sum_nonneg fun _ _ => abs_nonneg _

private theorem perturbation_allows (r e : ℕ) (c : ℕ → ℝ) :
    Allows (r + 4) (fun g : ℝ => g ^ 2 * polynomial r e c g) 0
      (mass r e c * monomialBudget r) := by
  have hterm (j : ℕ) (hj : j ∈ indices r e) :
      Allows (r + 4) (fun g : ℝ => c j * g ^ (j + 2)) 0
        (|c j| * monomialBudget r) := by
    have hj' := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
    have hk : j + 2 ≤ r + 2 := by omega
    simpa only [smul_eq_mul] using (monomial_allows r (j + 2) hk).smul (c j)
  have hs := allows_sum hterm
  have heq : (fun g : ℝ => g ^ 2 * polynomial r e c g) =
      (fun g : ℝ => ∑ j ∈ indices r e, c j * g ^ (j + 2)) := by
    funext g
    unfold polynomial
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    rw [pow_add]
    ring
  rw [heq]
  simpa only [mass, Finset.sum_mul] using hs

private theorem jet_le {d : ℕ} {f : ℝ → ℝ} {C : ℝ}
    (h : Allows d f 0 C) (n : ℕ) (hn : n ≤ d) :
    |jet f n 1| ≤ C := by
  have he : ‖iteratedFDeriv ℝ n f 0 (fun _ => (1 : ℝ))‖ ≤ C := by
    have hp := (iteratedFDeriv ℝ n f 0).le_opNorm (fun _ => (1 : ℝ))
    simp only [norm_one, Finset.prod_const_one, mul_one] at hp
    exact hp.trans (h.norm_le n hn)
  have hfpos : 0 < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hfone : (1 : ℝ) ≤ n.factorial := by
    exact_mod_cast (Nat.succ_le_of_lt (Nat.factorial_pos n))
  have hi : |(n.factorial : ℝ)⁻¹| ≤ 1 := by
    rw [abs_of_pos (inv_pos.mpr hfpos)]
    rw [inv_eq_one_div]
    exact (div_le_iff₀ hfpos).mpr (by simpa using hfone)
  change ‖jet f n 1‖ ≤ C
  simp only [jet, norm_smul, Real.norm_eq_abs]
  exact (mul_le_mul hi he (norm_nonneg _) zero_le_one).trans_eq (one_mul C)

theorem constant_pos (r : ℕ) : 0 < constant r := by
  have hm : 0 < modifierBudget r := lt_of_lt_of_le zero_lt_one (budget_one r modifier)
  have hp : 0 < monomialBudget r :=
    lt_of_lt_of_le zero_lt_one (budget_one r (fun k (t : ℝ) => t ^ k))
  unfold constant
  positivity

/-- The exact scalar prior modifier, at every requested jet order including0. -/
theorem finite_bound (r e : ℕ) (c : ℕ → ℝ) (q n : ℕ)
    (hq : q ≤ r + 2) (hn : n ≤ r + 4) :
    |jet (fun g : ℝ =>
      (1 + g ^ 2 * polynomial r e c g) *
        ((Real.sqrt (1 + g ^ 2 * polynomial r e c g))⁻¹) ^ q) n 1| ≤
      constant r * (1 + mass r e c) ^ (r + 4) := by
  let f : ℝ → ℝ := fun g => g ^ 2 * polynomial r e c g
  have hf : Allows (r + 4) f 0 (mass r e c * monomialBudget r) :=
    perturbation_allows r e c
  have hzero : f 0 = 0 := by simp [f]
  have hg : Allows (r + 4) (modifier q) (f 0) (modifierBudget r) := by
    rw [hzero]
    exact modifier_allows r q hq
  have hc := hg.comp hf
  have hbound := jet_le hc n hn
  have hm := mass_nonneg r e c
  have hp : 1 ≤ monomialBudget r := budget_one r (fun k (t : ℝ) => t ^ k)
  have hq' : 0 ≤ modifierBudget r := le_trans zero_le_one (budget_one r modifier)
  have hbase : 1 + mass r e c * monomialBudget r ≤
      monomialBudget r * (1 + mass r e c) := by nlinarith
  have hpow := pow_le_pow_left₀
    (show 0 ≤ 1 + mass r e c * monomialBudget r by positivity) hbase (r + 4)
  have hprice : composeCost (r + 4) (modifierBudget r)
      (mass r e c * monomialBudget r) ≤
      constant r * (1 + mass r e c) ^ (r + 4) := by
    unfold composeCost constant
    calc
      _ ≤ ((r + 4).factorial : ℝ) * modifierBudget r *
          (monomialBudget r * (1 + mass r e c)) ^ (r + 4) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = _ := by rw [mul_pow]; ring
  exact hbound.trans hprice

/-- Direct application to the original Plan's auxiliary prior. The coefficient
mass includes precisely j<e and j≤r-2; the period and level remain arbitrary. -/
theorem prior_bound {G : Gauge} {C : Family G} {N period r : ℕ}
    (P : Plan C N period r) (m e q n : ℕ) (hq : q ≤ r + 2) (hn : n ≤ r + 4) :
    |jet (fun g : ℝ =>
      (1 + g ^ 2 * (SelectedPlanTriangular.prior P e).poly m g) *
        ((Real.sqrt (1 + g ^ 2 *
          (SelectedPlanTriangular.prior P e).poly m g))⁻¹) ^ q) n 1| ≤
      constant r * (1 + ∑ j ∈ (Finset.range (r - 2 + 1)).filter (fun j => j < e),
        |P.coefficient m j|) ^ (r + 4) := by
  have heq : (SelectedPlanTriangular.prior P e).poly m =
      polynomial r e (P.coefficient m) := by
    funext g
    simp only [Plan.poly, SelectedPlanTriangular.prior, polynomial, indices,
      Finset.sum_filter, ite_mul, zero_mul]
  simpa only [heq, mass, indices] using finite_bound r e (P.coefficient m) q n hq hn

end YM.Integration.SelectedPlanPriorJetBound
end
