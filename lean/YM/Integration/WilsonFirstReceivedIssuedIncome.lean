import YM.Integration.WilsonFirstReceivedIssuedRowTaylor

/-! The complete Taylor invoice at an occupied external mask on the original
passport. Its centers belong to the physical set of marked positions. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonFirstReceivedIssuedIncome
open Finset Lattice Wilson RG Marker QuadraticLocal QuadraticLocal.Earn Exterior
open WilsonFirstReceivedIssuedRowTaylor
open scoped Classical BigOperators

variable {G : Gauge} {n : Side} {V α ι : Type} [DecidableEq V] {P : Passport n V} {R : Census V}
variable (M : ι → Row P R G α) (w : V → ℝ) (hw : ∀ v, 0 < w v)

include hw in
theorem salary {τ c : ℝ} (hτ : 0 ≤ τ) (offer : Offers M w τ c) (s : R.Mode) :
    SumBudget (fun i => if (M i).mode = s then Poly.toll w s * (M i).salary else 0)
      ((s.val.image P.origin).card * c) := by
  let fee (o : Site n) (i : ι) := if (M i).center = o then
    Poly.toll w (M i).mode * (M i).height τ else 0
  have purchase (o : Site n) : SumBudget (fee o) c := offer o
  have union (F : Finset (Site n)) : SumBudget (fun i => ∑ o ∈ F, fee o i) ((F.card : ℝ) * c) := by
    induction F using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty, Finset.card_empty, Nat.cast_zero, zero_mul]
      exact ⟨fun _ => le_rfl, summable_zero, by simp⟩
    | @insert o F absent ih =>
      simpa only [Finset.sum_insert absent, Finset.card_insert_of_notMem absent, Nat.cast_add,
        Nat.cast_one, add_mul, one_mul, add_comm c] using Push.Local.sumBudget_add (purchase o) ih
  let sites := s.val.image P.origin
  refine Push.PriceCompiler.sumBudget_mono (union sites) ?_ ?_ le_rfl
  · intro i
    split
    · exact mul_nonneg (Poly.worth hw s).le (M i).sound.le
    · exact le_rfl
  · intro i
    change (if (M i).mode = s then Poly.toll w s * (M i).salary else 0) ≤ ∑ o ∈ sites, fee o i
    by_cases h : (M i).mode = s
    · have front : (M i).center ∈ sites := Finset.mem_image_of_mem P.origin (h ▸ (M i).binder.east)
      have taller : (M i).salary ≤ (M i).height τ := by
        unfold Row.height
        exact le_mul_of_one_le_right (M i).sound.le (Real.one_le_exp (by positivity))
      rw [if_pos h]
      calc
        _ ≤ fee (M i).center i := by
          simpa [fee, h] using mul_le_mul_of_nonneg_left taller (Poly.worth hw s).le
        _ ≤ _ := Finset.single_le_sum (fun o _ => (purchase o).1 i) front
    · rw [if_neg h]
      exact Finset.sum_nonneg fun o _ => (purchase o).1 i

include hw in
theorem filed {τ σ c : ℝ} (hτ : 0 ≤ τ) (hs : 0 < σ) (offer : Offers M w τ c)
    (paid : ∀ i, (M i).Budget) {K : ℕ} {p : V → ℕ} (due : Issues M σ K p)
    {g : ℝ} (hg : 0 < g) (hu : g ≤ 1) (u : α) (a : fieldDir G n 1)
    {A : ℝ} (ha : 0 ≤ A) (axis : ∀ e, ‖collect G a e‖ ≤ A) (q : ℕ) (s : R.Mode) (z : ℝ) :
    let d := q + ∑ v ∈ s.val, p v
    let C := (2 * (G.colorScale * A) * |z| / σ) ^ (d + 1) * g ^ q
    SumBudget (fun i => if (M i).mode = s then Poly.toll w s *
        ‖(M i).nominal g u (Comparison.RG02.Integral.sample g (z • a)) -
          (column (M i) g u (collect G a) d).eval (z : ℂ)‖ else 0)
      (C * ((s.val.image P.origin).card * c)) := by
  intro d C
  have hC : 0 ≤ C := by
    have positive := G.colorScale_pos
    dsimp only [C]
    positivity
  refine Push.PriceCompiler.sumBudget_mono
    (Push.Local.sumBudget_mul_left (salary M w hw hτ offer s) hC) ?_ ?_ le_rfl
  · intro i
    split
    · exact mul_nonneg (Poly.worth hw s).le (norm_nonneg _)
    · exact le_rfl
  · intro i
    by_cases h : (M i).mode = s
    · simp only [if_pos h]
      have toll := (due.usable i).2
      rw [h] at toll
      have eqd : q + (M i).lamp.toll = d := by rw [toll]
      have one := WilsonFirstReceivedIssuedRowTaylor.filed (M i) (paid i) hs (due.spend i)
        hg hu u a ha axis q z
      rw [eqd] at one
      rw [evaluated]
      calc
        _ ≤ Poly.toll w s * ((M i).salary * (2 * (G.colorScale * A) * |z| / σ) ^ (d + 1) *
            g ^ q) := mul_le_mul_of_nonneg_left one (Poly.worth hw s).le
        _ = _ := by dsimp only [C]; ring
    · simp [h]

end YM.Integration.WilsonFirstReceivedIssuedIncome
