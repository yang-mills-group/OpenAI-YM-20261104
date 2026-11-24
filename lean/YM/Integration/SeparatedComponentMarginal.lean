import YM.Integration.MonomialListMixedMarginal

/-! Add the main, quadratic and listed components in the original mixed-slot
marginal. Three distinct tags preserve the prefix terms; every list occurrence
is retained. -/

set_option autoImplicit false
noncomputable section
namespace YM.Integration.SeparatedComponentMarginal

open Function
open scoped BigOperators Classical

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The complete separated function, with the original signed subtraction. -/
def separated {α : Type*} (m l h : E → ℝ) (rows : List α)
    (q : α → ℕ) (f : α → E → ℝ) (z : ℝ × E) : ℝ :=
  m z.2 + z.1 ^ 2 * (l z.2 - h z.2) +
    (rows.map (fun a => z.1 ^ q a * f a z.2)).sum

private inductive Component (α : Type*)
  | main
  | light
  | heavy
  | row (a : α)

variable {ι : Type} [Fintype ι]

/-- Component field marginals pay the full separated mixed marginal.
No bound on the natural exponents and no removal of duplicate rows is used. -/
theorem marginal {α : Type*} (rows : List α) (q : α → ℕ)
    (f : α → E → ℝ) (m l h : E → ℝ)
    (hm : AnalyticAt ℝ m 0) (hl : AnalyticAt ℝ l 0)
    (hh : AnalyticAt ℝ h 0) (hf : ∀ a ∈ rows, AnalyticAt ℝ (f a) 0)
    (c d : ℕ) (v : ι → E) (j : Fin (d + 1)) (i0 : ι)
    (σ : Equiv.Perm (Fin (c + (d + 1))))
    (Am Al Ah : ℝ) (A : α → ℝ)
    (hAm : (∑ u : Fin d → ι,
      ‖(((d + 1).factorial : ℝ)⁻¹) *
        iteratedFDeriv ℝ (d + 1) m 0
          (fun t => v (Fin.insertNth (α := fun _ => ι) j i0 u t))‖) ≤ Am)
    (hAl : (∑ u : Fin d → ι,
      ‖(((d + 1).factorial : ℝ)⁻¹) *
        iteratedFDeriv ℝ (d + 1) l 0
          (fun t => v (Fin.insertNth (α := fun _ => ι) j i0 u t))‖) ≤ Al)
    (hAh : (∑ u : Fin d → ι,
      ‖(((d + 1).factorial : ℝ)⁻¹) *
        iteratedFDeriv ℝ (d + 1) h 0
          (fun t => v (Fin.insertNth (α := fun _ => ι) j i0 u t))‖) ≤ Ah)
    (hA : ∀ a ∈ rows, (∑ u : Fin d → ι,
      ‖(((d + 1).factorial : ℝ)⁻¹) *
        iteratedFDeriv ℝ (d + 1) (f a) 0
          (fun t => v (Fin.insertNth (α := fun _ => ι) j i0 u t))‖) ≤ A a) :
    (∑ u : Fin d → ι,
      ‖(((c + (d + 1)).factorial : ℝ)⁻¹) *
        iteratedFDeriv ℝ (c + (d + 1))
          (separated m l h rows q f) 0
          (NativeMixedSlotProduct.slots c
            (fun t => v (Fin.insertNth (α := fun _ => ι) j i0 u t)) ∘ σ)‖) ≤
      Am + Al + Ah + (rows.map A).sum := by
  let requests : List (Component α) :=
    .main :: .light :: .heavy :: rows.map Component.row
  let degree : Component α → ℕ
    | .main => 0
    | .light => 2
    | .heavy => 2
    | .row a => q a
  let field : Component α → E → ℝ
    | .main => m
    | .light => l
    | .heavy => -h
    | .row a => f a
  let price : Component α → ℝ
    | .main => Am
    | .light => Al
    | .heavy => Ah
    | .row a => A a
  have hfield : ∀ a ∈ requests, AnalyticAt ℝ (field a) 0 := by
    intro a ha
    cases a with
    | main => exact hm
    | light => exact hl
    | heavy => exact hh.neg
    | row a =>
        exact hf a (by simpa [requests] using ha)
  have hprice_bound : ∀ a ∈ requests, (∑ u : Fin d → ι,
      ‖(((d + 1).factorial : ℝ)⁻¹) *
        iteratedFDeriv ℝ (d + 1) (field a) 0
          (fun t => v (Fin.insertNth (α := fun _ => ι) j i0 u t))‖) ≤ price a := by
    intro a ha
    cases a with
    | main => exact hAm
    | light => exact hAl
    | heavy =>
        simpa only [field, price, iteratedFDeriv_neg_apply, neg_apply,
          mul_neg, norm_neg] using hAh
    | row a =>
        exact hA a (by simpa [requests] using ha)
  have hb := MonomialListMixedMarginal.list_marginal
    requests degree field price hfield c d v j i0 σ hprice_bound
  have hfunction :
      (fun z : ℝ × E =>
        (requests.map (fun a => z.1 ^ degree a * field a z.2)).sum) =
        separated m l h rows q f := by
    funext z
    simp only [requests, List.map_cons, List.sum_cons, List.map_map,
      Function.comp_def, degree, field, separated, pow_zero, one_mul, Pi.neg_apply]
    ring
  have hprice : (requests.map price).sum = Am + Al + Ah + (rows.map A).sum := by
    simp only [requests, List.map_cons, List.sum_cons, List.map_map,
      Function.comp_def, price]
    ring
  rw [hfunction, hprice] at hb
  exact hb

end YM.Integration.SeparatedComponentMarginal
end
