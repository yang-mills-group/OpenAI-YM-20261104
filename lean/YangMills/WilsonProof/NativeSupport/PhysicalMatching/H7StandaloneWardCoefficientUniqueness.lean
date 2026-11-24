import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

noncomputable section
open Filter
open scoped BigOperators Topology
namespace PhysicalMatching.H7StandaloneWardCoefficientUniqueness

def crop (p : ℕ) (t : ℝ) (a : ℕ → ℂ) : ℂ :=
  ∑ i ∈ Finset.range (p+1), (t : ℂ)^i * a i

def Reading {α : Type*} (l : Filter α) (t : α → ℝ) (physical : α → ℂ) (a : ℕ → ℂ) : Prop :=
  ∀ p, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ r in l,
    ‖physical r - crop p (t r) a‖ ≤ C * |t r|^(p+1)

def Residual {α : Type*} (l : Filter α) (t : α → ℝ) (physical : α → ℂ) : Prop :=
  ∀ p : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ r in l, ‖physical r‖ ≤ C * |t r|^(p+1)

theorem cropSub (p : ℕ) (t : ℝ) (a b : ℕ → ℂ) :
    crop p t (fun i => a i - b i) = crop p t a - crop p t b := by
  simp only [crop, mul_sub, Finset.sum_sub_distrib]

theorem vanishing {α : Type*} {l : Filter α} [NeBot l] {t : α → ℝ}
    (positive : ∀ᶠ r in l, 0 < t r) (zero : Tendsto t l (𝓝 0))
    (a : ℕ → ℂ) (price : ∀ p, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ r in l,
      ‖crop p (t r) a‖ ≤ C * |t r|^(p+1)) : ∀ k, a k = 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k previous =>
    obtain ⟨C, hC, hp⟩ := price k
    by_contra ha
    have hn : 0 < ‖a k‖ := norm_pos_iff.mpr ha
    have hden : 0 < C+1 := by linarith
    have hsmall : ∀ᶠ r in l, t r < ‖a k‖/(C+1) :=
      (tendsto_order.1 zero).2 _ (div_pos hn hden)
    obtain ⟨r, hr, hs, paid⟩ := (positive.and (hsmall.and hp)).exists
    have lower : (∑ i ∈ Finset.range k, (t r : ℂ)^i * a i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [previous i (Finset.mem_range.mp hi), mul_zero]
    have top : crop k (t r) a = (t r : ℂ)^k * a k := by
      simp only [crop, Finset.sum_range_succ, lower, zero_add]
    rw [top, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
      pow_succ] at paid
    have hs' := (lt_div_iff₀ hden).mp hs
    have strict : C*t r < ‖a k‖ := by nlinarith only [hs',hr]
    have impossible := mul_pos (pow_pos hr k) (sub_pos.mpr strict)
    nlinarith only [paid,impossible]

theorem throughResidual {α : Type*} {l : Filter α} [NeBot l] {t : α → ℝ}
    (positive : ∀ᶠ r in l, 0 < t r) (zero : Tendsto t l (𝓝 0))
    {x y : α → ℂ} {a b : ℕ → ℂ}
    (left : Reading l t x a) (right : Reading l t y b)
    (physical : Residual l t (fun r => x r - y r)) : ∀ k, a k = b k := by
  apply fun k => sub_eq_zero.mp ?_
  apply vanishing positive zero (fun i => a i - b i)
  intro p
  obtain ⟨A, hA, left⟩ := left p
  obtain ⟨B, hB, right⟩ := right p
  obtain ⟨D, hD, physical⟩ := physical p
  refine ⟨A+D+B, by linarith, ?_⟩
  filter_upwards [left, physical, right] with r h₁ h₂ h₃
  rw [cropSub]
  let v := crop p (t r) a
  let w := crop p (t r) b
  change ‖v-w‖ ≤ (A+D+B)*|t r|^(p+1)
  have decomp : v-w = (-(x r-v)+(x r-y r))+(y r-w) := by ring
  rw [decomp]
  calc
    _ ≤ ‖-(x r-v)+(x r-y r)‖ + ‖y r-w‖ := norm_add_le _ _
    _ ≤ (‖x r-v‖ + ‖x r-y r‖) + ‖y r-w‖ := by
      simpa only [norm_neg] using add_le_add (norm_add_le (-(x r-v)) (x r-y r)) (le_refl ‖y r-w‖)
    _ ≤ _ := by
      change ‖x r-crop p (t r) a‖ + ‖x r-y r‖ + ‖y r-crop p (t r) b‖ ≤ _
      nlinarith only [h₁,h₂,h₃]

theorem exactResidual {α : Type*} {l : Filter α} (t : α → ℝ) {x y : α → ℂ}
    (he : x =ᶠ[l] y) : Residual l t (fun r => x r-y r) := by
  intro p
  refine ⟨0,le_rfl,?_⟩
  filter_upwards [he] with r hr
  simp [hr]

theorem smallResidual {α : Type*} {l : Filter α} {t : α → ℝ}
    (positive : ∀ᶠ r in l, 0 < t r) {e : α → ℂ}
    (small : ∀ k : ℕ, Tendsto (fun r => ‖e r‖/(t r)^k) l (𝓝 0)) : Residual l t e := by
  intro p
  refine ⟨1,zero_le_one,?_⟩
  have bound := (tendsto_order.1 (small (p+1))).2 (1 : ℝ) zero_lt_one
  filter_upwards [positive,bound] with r hr hb
  have hpow : 0 < (t r)^(p+1) := pow_pos hr _
  simpa only [abs_of_pos hr,one_mul] using ((div_lt_iff₀ hpow).mp hb).le

theorem original {α : Type*} {l : Filter α} [NeBot l] {t : α → ℝ}
    (positive : ∀ᶠ r in l, 0 < t r) (zero : Tendsto t l (𝓝 0))
    {x y : α → ℂ} {a b : ℕ → ℂ}
    (left : Reading l t x a) (right : Reading l t y b)
    (small : ∀ k : ℕ, Tendsto (fun r => ‖x r-y r‖/(t r)^k) l (𝓝 0)) :
    ∀ k, a k = b k :=
  throughResidual positive zero left right (smallResidual positive small)

end PhysicalMatching.H7StandaloneWardCoefficientUniqueness

