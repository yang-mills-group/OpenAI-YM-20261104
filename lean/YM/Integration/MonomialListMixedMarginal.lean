import YM.Integration.MixedSlotMarginal
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! A monomial coupling factor has normalized coefficients zero or one.
Sum the resulting fixed-field-port estimate over the actual list, retaining
every repeated row and the original mixed-slot order and factorial. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.MonomialListMixedMarginal

open Function
open Comparison.RG02.Assembly
open scoped BigOperators ContDiff Classical

/-- Every normalized coefficient of a nonnegative integral monomial is at most one. -/
theorem monomial_jet_le (c q : ℕ) :
    |jet (fun g : ℝ => g ^ q) c 1| ≤ 1 := by
  unfold jet
  rw [← iteratedDeriv_eq_iteratedFDeriv, smul_eq_mul,
    iteratedDeriv_fun_pow_zero]
  by_cases h : c = q
  · subst c
    have hq : (q.factorial : ℝ) ≠ 0 := by positivity
    simp [hq]
  · simp [h]

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem list_smooth {α : Type*} (q : α → ℕ) (f : α → E → ℝ)
    (l : List α) (hf : ∀ a ∈ l, AnalyticAt ℝ (f a) 0) :
    ContDiffAt ℝ ω
      (fun z : ℝ × E => (l.map (fun a => z.1 ^ q a * f a z.2)).sum) 0 := by
  revert hf
  induction l with
  | nil =>
      intro _
      exact contDiffAt_const
  | cons a l ih =>
      intro hf
      have hfa := hf a (by simp)
      have hfl : ∀ b ∈ l, AnalyticAt ℝ (f b) 0 := by
        intro b hb
        exact hf b (by simp only [List.mem_cons]; exact Or.inr hb)
      have ha : ContDiffAt ℝ ω
          (fun z : ℝ × E => z.1 ^ q a * f a z.2) 0 :=
        (contDiffAt_fst.pow (q a)).mul (hfa.contDiffAt.comp 0 contDiffAt_snd)
      exact ha.add (ih hfl)

variable {ι : Type} [Fintype ι]

/-- Full fixed-port marginal of the literal finite layer, including duplicate rows. -/
theorem list_marginal {α : Type*} (l : List α) (q : α → ℕ)
    (f : α → E → ℝ) (A : α → ℝ)
    (hf : ∀ a ∈ l, AnalyticAt ℝ (f a) 0)
    (c d : ℕ) (v : ι → E) (j : Fin (d + 1)) (i0 : ι)
    (σ : Equiv.Perm (Fin (c + (d + 1))))
    (hA : ∀ a ∈ l, (∑ u : Fin d → ι,
      ‖(((d + 1).factorial : ℝ)⁻¹) *
        iteratedFDeriv ℝ (d + 1) (f a) 0
          (fun t => v (Fin.insertNth (α := fun _ => ι) j i0 u t))‖) ≤ A a) :
    (∑ u : Fin d → ι,
      ‖(((c + (d + 1)).factorial : ℝ)⁻¹) *
        iteratedFDeriv ℝ (c + (d + 1))
          (fun z : ℝ × E => (l.map (fun a => z.1 ^ q a * f a z.2)).sum) 0
          (NativeMixedSlotProduct.slots c
            (fun t => v (Fin.insertNth (α := fun _ => ι) j i0 u t)) ∘ σ)‖) ≤
      (l.map A).sum := by
  revert hf hA
  induction l with
  | nil =>
      intro _ _
      simp
  | cons a l ih =>
      intro hf hA
      have hfa := hf a (by simp)
      have haa := hA a (by simp)
      have hfl : ∀ b ∈ l, AnalyticAt ℝ (f b) 0 := by
        intro b hb
        exact hf b (by simp only [List.mem_cons]; exact Or.inr hb)
      have hAl : ∀ b ∈ l, (∑ u : Fin d → ι,
          ‖(((d + 1).factorial : ℝ)⁻¹) *
            iteratedFDeriv ℝ (d + 1) (f b) 0
              (fun t => v (Fin.insertNth (α := fun _ => ι) j i0 u t))‖) ≤ A b := by
        intro b hb
        exact hA b (by simp only [List.mem_cons]; exact Or.inr hb)
      have ha0 : 0 ≤ A a := (Finset.sum_nonneg (fun _ _ => norm_nonneg _)).trans haa
      have hh : AnalyticAt ℝ (fun g : ℝ => g ^ q a) 0 := analyticAt_id.pow _
      have hp := MixedSlotMarginal.product_marginal hh hfa c d v j i0 σ haa
      have hb := hp.trans
        ((mul_le_mul_of_nonneg_right (monomial_jet_le c (q a)) ha0).trans_eq (one_mul _))
      let H := NativeMixedSlotProduct.product (fun g : ℝ => g ^ q a) (f a)
      let F := fun z : ℝ × E => (l.map (fun b => z.1 ^ q b * f b z.2)).sum
      let w := fun u : Fin d → ι => NativeMixedSlotProduct.slots c
        (fun t => v (Fin.insertNth (α := fun _ => ι) j i0 u t)) ∘ σ
      let t : ℝ := ((c + (d + 1)).factorial : ℝ)⁻¹
      have hH : ContDiffAt ℝ (c + (d + 1)) H 0 :=
        (hh.contDiffAt.comp 0 contDiffAt_fst).mul
          (hfa.contDiffAt.comp 0 contDiffAt_snd)
      have hF : ContDiffAt ℝ (c + (d + 1)) F 0 :=
        (list_smooth q f l hfl).of_le le_top
      change (∑ u : Fin d → ι,
        ‖t * iteratedFDeriv ℝ (c + (d + 1)) (H + F) 0 (w u)‖) ≤ A a + (l.map A).sum
      calc
        _ = ∑ u : Fin d → ι,
            ‖t * iteratedFDeriv ℝ (c + (d + 1)) H 0 (w u) +
              t * iteratedFDeriv ℝ (c + (d + 1)) F 0 (w u)‖ := by
          apply Finset.sum_congr rfl
          intro u _
          rw [iteratedFDeriv_add_apply hH hF, add_apply, mul_add]
        _ ≤ ∑ u : Fin d → ι,
            (‖t * iteratedFDeriv ℝ (c + (d + 1)) H 0 (w u)‖ +
              ‖t * iteratedFDeriv ℝ (c + (d + 1)) F 0 (w u)‖) :=
          Finset.sum_le_sum (fun _ _ => norm_add_le _ _)
        _ = (∑ u : Fin d → ι, ‖t * iteratedFDeriv ℝ (c + (d + 1)) H 0 (w u)‖) +
            (∑ u : Fin d → ι, ‖t * iteratedFDeriv ℝ (c + (d + 1)) F 0 (w u)‖) :=
          Finset.sum_add_distrib
        _ ≤ A a + (l.map A).sum := add_le_add hb (ih hfl hAl)

end YM.Integration.MonomialListMixedMarginal
end
