import YM.Comparison.RG02.Assembly.Contact
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Data.Nat.Choose.Basic

/-!
# Exact normalized Cauchy products and centered occurrence sums

The jet is the original Assembly.jet. Restriction to a line and the finite
Leibniz formula preserve the full scalar modifier and nonlinear field.
The list bound retains every original occurrence, including duplicates.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Integration.NormalizedJetCauchy

open Finset Function
open YM.Comparison.RG02.Assembly
open scoped BigOperators ContDiff Topology

private lemma factorial_weight (n c : ℕ) (hc : c ≤ n) :
    (n.factorial : ℝ)⁻¹ * (n.choose c : ℝ) =
      (c.factorial : ℝ)⁻¹ * ((n - c).factorial : ℝ)⁻¹ := by
  have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hc0 : (c.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero c
  have hd0 : ((n - c).factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (n - c)
  have he : (n.choose c : ℝ) * (c.factorial : ℝ) *
      ((n - c).factorial : ℝ) = (n.factorial : ℝ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hc
  rw [← mul_inv]
  apply mul_right_cancel₀ (mul_ne_zero hc0 hd0)
  rw [inv_mul_cancel₀ (mul_ne_zero hc0 hd0)]
  calc
    _ = (n.factorial : ℝ)⁻¹ *
        ((n.choose c : ℝ) * (c.factorial : ℝ) * ((n - c).factorial : ℝ)) := by ring
    _ = 1 := by rw [he, inv_mul_cancel₀ hn]

private lemma scalar_product (h f : ℝ → ℝ)
    (hh : ContDiffAt ℝ ω h 0) (hf : ContDiffAt ℝ ω f 0) (n : ℕ) :
    jet (fun t => h t * f t) n 1 =
      ∑ c ∈ range (n + 1), jet h c 1 * jet f (n - c) 1 := by
  change (n.factorial : ℝ)⁻¹ * iteratedDeriv n (h * f) 0 =
    ∑ c ∈ range (n + 1),
      ((c.factorial : ℝ)⁻¹ * iteratedDeriv c h 0) *
        (((n - c).factorial : ℝ)⁻¹ * iteratedDeriv (n - c) f 0)
  rw [iteratedDeriv_mul (hh.of_le le_top) (hf.of_le le_top), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  calc
    _ = ((n.factorial : ℝ)⁻¹ * (n.choose c : ℝ)) *
        (iteratedDeriv c h 0 * iteratedDeriv (n - c) f 0) := by ring
    _ = _ := by
      rw [factorial_weight n c (Nat.le_of_lt_succ (mem_range.mp hc))]
      ring

private lemma list_sum_sub {ι : Type*} (l : List ι) (f g : ι → ℝ) :
    (l.map f).sum - (l.map g).sum = (l.map fun a => f a - g a).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [← ih]
      ring

private lemma list_sum_finset {ι : Type*} (l : List ι) (s : Finset ℕ)
    (f : ι → ℕ → ℝ) :
    (l.map fun a => ∑ c ∈ s, f a c).sum =
      ∑ c ∈ s, (l.map fun a => f a c).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [Finset.sum_add_distrib, ih]

private lemma list_weighted_norm {ι : Type*} (l : List ι) (u v : ι → ℝ)
    (H : ℝ) (hu : ∀ a ∈ l, ‖u a‖ ≤ H) :
    ‖(l.map fun a => u a * v a).sum‖ ≤ H * (l.map fun a => ‖v a‖).sum := by
  revert hu
  induction l with
  | nil =>
      intro _hu
      simp
  | cons a l ih =>
      intro hu
      have hl : ∀ b ∈ l, ‖u b‖ ≤ H :=
        fun b hb => hu b (List.mem_cons_of_mem a hb)
      simp only [List.map_cons, List.sum_cons]
      calc
        _ ≤ ‖u a * v a‖ + ‖(l.map fun b => u b * v b).sum‖ := norm_add_le _ _
        _ ≤ H * ‖v a‖ + H * (l.map fun b => ‖v b‖).sum := by
          rw [norm_mul]
          exact add_le_add
            (mul_le_mul_of_nonneg_right (hu a (List.mem_cons_self ..)) (norm_nonneg _))
            (ih hl)
        _ = _ := by ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Exact Cauchy formula for the original normalized joint jet. -/
theorem product_jet (h : ℝ → ℝ) (f : E → ℝ)
    (hh : ContDiffAt ℝ ω h 0) (hf : ContDiffAt ℝ ω f 0) (n : ℕ) (A : E) :
    jet (fun z : ℝ × E => h z.1 * f z.2) n (1, A) =
      ∑ c ∈ range (n + 1), jet h c 1 * jet f (n - c) A := by
  let P : ℝ × E → ℝ := fun z => h z.1 * f z.2
  let L : ℝ →L[ℝ] ℝ × E := ContinuousLinearMap.toSpanSingleton ℝ (1, A)
  let LA : ℝ →L[ℝ] E := ContinuousLinearMap.toSpanSingleton ℝ A
  have hP : ContDiffAt ℝ ω P 0 :=
    (hh.comp (0 : ℝ × E) contDiffAt_fst).mul
      (hf.comp (0 : ℝ × E) contDiffAt_snd)
  have hf0 : ContDiffAt ℝ ω f (LA 0) := LA.map_zero.symm ▸ hf
  have hfa : ContDiffAt ℝ ω (f ∘ LA) 0 :=
    hf0.comp 0 LA.contDiff.contDiffAt
  have he : P ∘ L = fun t => h t * (f ∘ LA) t := by
    funext t
    simp [P, L, LA]
  calc
    _ = jet (P ∘ L) n 1 := by
      symm
      simpa [P, L] using jet_continuous_right L (hP.of_le le_top) (1 : ℝ)
    _ = ∑ c ∈ range (n + 1), jet h c 1 * jet (f ∘ LA) (n - c) 1 := by
      rw [he]
      exact scalar_product h (f ∘ LA) hh hfa n
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c _hc
      rw [jet_continuous_right LA (hf.of_le le_top)]
      simp [LA]

/-- Center only the field direction; the scalar direction stays equal to one. -/
theorem centered_product_jet (h : ℝ → ℝ) (f : E → ℝ)
    (hh : ContDiffAt ℝ ω h 0) (hf : ContDiffAt ℝ ω f 0) (n : ℕ) (A : E) :
    jet (fun z : ℝ × E => h z.1 * f z.2) n (1, A) -
      jet (fun z : ℝ × E => h z.1 * f z.2) n (1, 0) =
        ∑ c ∈ range (n + 1),
          jet h c 1 * (jet f (n - c) A - jet f (n - c) 0) := by
  rw [product_jet h f hh hf n A, product_jet h f hh hf n 0,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro c _hc
  ring

/-- The complete centered product is paid by the finite Cauchy convolution. -/
theorem centered_product_bound (h : ℝ → ℝ) (f : E → ℝ)
    (hh : ContDiffAt ℝ ω h 0) (hf : ContDiffAt ℝ ω f 0)
    (n : ℕ) (A : E) (H F : ℝ) (hH : 0 ≤ H) (_hF : 0 ≤ F)
    (hs : ∀ c ≤ n, ‖jet h c 1‖ ≤ H)
    (hb : ∀ k ≤ n, ‖jet f k A - jet f k 0‖ ≤ F) :
    ‖jet (fun z : ℝ × E => h z.1 * f z.2) n (1, A) -
      jet (fun z : ℝ × E => h z.1 * f z.2) n (1, 0)‖ ≤
        (n + 1 : ℝ) * H * F := by
  rw [centered_product_jet h f hh hf n A]
  calc
    _ ≤ ∑ c ∈ range (n + 1),
        ‖jet h c 1 * (jet f (n - c) A - jet f (n - c) 0)‖ := norm_sum_le _ _
    _ ≤ ∑ _c ∈ range (n + 1), H * F := by
      apply Finset.sum_le_sum
      intro c hc
      rw [norm_mul]
      exact mul_le_mul (hs c (Nat.le_of_lt_succ (mem_range.mp hc)))
        (hb (n - c) (Nat.sub_le _ _)) (norm_nonneg _) hH
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        Nat.cast_add, Nat.cast_one]
      ring

private lemma list_smooth {ι : Type*} (l : List ι) (f : ι → E → ℝ)
    (h : ∀ a ∈ l, ContDiffAt ℝ ω (f a) 0) :
    ContDiffAt ℝ ω (fun z => (l.map fun a => f a z).sum) 0 := by
  revert h
  induction l with
  | nil =>
      intro _h
      simp only [List.map_nil, List.sum_nil]
      exact contDiffAt_const
  | cons a l ih =>
      intro h
      simp only [List.map_cons, List.sum_cons]
      exact (h a (List.mem_cons_self ..)).add
        (ih (fun b hb => h b (List.mem_cons_of_mem a hb)))

private lemma list_jet {ι : Type*} (l : List ι) (f : ι → E → ℝ)
    (h : ∀ a ∈ l, ContDiffAt ℝ ω (f a) 0) (n : ℕ) (A : E) :
    jet (fun z => (l.map fun a => f a z).sum) n A =
      (l.map fun a => jet (f a) n A).sum := by
  revert h
  induction l with
  | nil =>
      intro _h
      simpa only [List.map_nil, List.sum_nil] using
        (GradeAt.grade_zero (n + 1) : GradeAt (n + 1) (fun _ : E => (0 : ℝ))).jet_z
          A (by omega : n < n + 1)
  | cons a l ih =>
      intro h
      have hl : ∀ b ∈ l, ContDiffAt ℝ ω (f b) 0 :=
        fun b hb => h b (List.mem_cons_of_mem a hb)
      simp only [List.map_cons, List.sum_cons]
      rw [show (fun z => f a z + (l.map fun b => f b z).sum) =
        f a + (fun z => (l.map fun b => f b z).sum) from rfl]
      unfold jet
      rw [iteratedFDeriv_add_apply ((h a (List.mem_cons_self ..)).of_le le_top)
        ((list_smooth l f hl).of_le le_top), add_apply, smul_add]
      exact congrArg (fun y => jet (f a) n A + y) (ih hl)

/-- Different scalar modifiers may be used at every original list occurrence.
Only the sum of centered field jets is paid, with all duplicates retained. -/
theorem list_centered_product_bound {ι : Type*} (l : List ι)
    (h : ι → ℝ → ℝ) (f : ι → E → ℝ)
    (hh : ∀ a ∈ l, ContDiffAt ℝ ω (h a) 0)
    (hf : ∀ a ∈ l, ContDiffAt ℝ ω (f a) 0)
    (n : ℕ) (A : E) (H F : ℝ) (hH : 0 ≤ H) (_hF : 0 ≤ F)
    (hs : ∀ a ∈ l, ∀ c ≤ n, ‖jet (h a) c 1‖ ≤ H)
    (hb : ∀ k ≤ n, (l.map fun a => ‖jet (f a) k A - jet (f a) k 0‖).sum ≤ F) :
    ‖jet (fun z : ℝ × E => (l.map fun a => h a z.1 * f a z.2).sum) n (1, A) -
      jet (fun z : ℝ × E => (l.map fun a => h a z.1 * f a z.2).sum) n (1, 0)‖ ≤
        (n + 1 : ℝ) * H * F := by
  let p : ι → ℝ × E → ℝ := fun a z => h a z.1 * f a z.2
  have hp : ∀ a ∈ l, ContDiffAt ℝ ω (p a) 0 := by
    intro a ha
    exact ((hh a ha).comp (0 : ℝ × E) contDiffAt_fst).mul
      ((hf a ha).comp (0 : ℝ × E) contDiffAt_snd)
  have he :
      jet (fun z => (l.map fun a => p a z).sum) n (1, A) -
        jet (fun z => (l.map fun a => p a z).sum) n (1, 0) =
      ∑ c ∈ range (n + 1),
        (l.map fun a => jet (h a) c 1 *
          (jet (f a) (n - c) A - jet (f a) (n - c) 0)).sum := by
    rw [list_jet l p hp n (1, A), list_jet l p hp n (1, 0), list_sum_sub]
    calc
      _ = (l.map fun a => ∑ c ∈ range (n + 1),
          jet (h a) c 1 * (jet (f a) (n - c) A - jet (f a) (n - c) 0)).sum := by
        apply congrArg List.sum
        apply List.map_congr_left
        intro a ha
        exact centered_product_jet (h a) (f a) (hh a ha) (hf a ha) n A
      _ = _ := list_sum_finset l (range (n + 1)) _
  change ‖jet (fun z => (l.map fun a => p a z).sum) n (1, A) -
    jet (fun z => (l.map fun a => p a z).sum) n (1, 0)‖ ≤ _
  rw [he]
  calc
    _ ≤ ∑ c ∈ range (n + 1),
        ‖(l.map fun a => jet (h a) c 1 *
          (jet (f a) (n - c) A - jet (f a) (n - c) 0)).sum‖ := norm_sum_le _ _
    _ ≤ ∑ _c ∈ range (n + 1), H * F := by
      apply Finset.sum_le_sum
      intro c hc
      exact (list_weighted_norm l (fun a => jet (h a) c 1)
        (fun a => jet (f a) (n - c) A - jet (f a) (n - c) 0) H
        (fun a ha => hs a ha c (Nat.le_of_lt_succ (mem_range.mp hc)))).trans
          (mul_le_mul_of_nonneg_left (hb (n - c) (Nat.sub_le _ _)) hH)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        Nat.cast_add, Nat.cast_one]
      ring

end YM.Integration.NormalizedJetCauchy
end
