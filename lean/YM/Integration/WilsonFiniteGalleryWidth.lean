import YM.Integration.WilsonThermometerUnpaintedCapture

/-! A finite torus permits a qualitative change of the support exponent when
establishing Haar integrability. The finite-volume fee is kept out of the
quantitative two-amplitude estimate. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonFiniteGalleryWidth
open Finset Lattice RG Ac Wilson Marker QuadraticLocal Push.AbsoluteSums
open scoped Classical BigOperators

theorem paid {G : Gauge} {n : Side} {p : BudgetPoint} {V X I : Type}
    [Fintype V] [DecidableEq V] {R : Census V} {o : V → Site n}
    (L : Lamps X I G p o R) {B : ℕ} {w : V → ℝ} (hp : ∀j, 0 < w j) {a b C : ℝ}
    (h : L.Paid w B a C) :
    ∃ E : ℝ, 0 < E ∧ L.Paid w B b E := by
  let d := (univ : Finset (Support n)).sup (coverNumber B)
  let t := Real.exp (max 0 (b-a) * (d:ℝ))
  have tpos : 0 < t := Real.exp_pos _
  have length (j:I) : (coverNumber B (L.ground j):ℝ) ≤ (d:ℝ) := by
    exact_mod_cast (Finset.le_sup (f:=coverNumber B) (mem_univ (L.ground j)))
  have factor (j:I) : Real.exp (b * coverNumber B (L.ground j)) ≤
      t * Real.exp (a * coverNumber B (L.ground j)) := by
    dsimp [t]
    rw [←Real.exp_add, Real.exp_le_exp]
    have step := mul_le_mul_of_nonneg_right (le_max_right 0 (b-a))
      (Nat.cast_nonneg (α:=ℝ) (coverNumber B (L.ground j)))
    have top := mul_le_mul_of_nonneg_left (length j) (le_max_left 0 (b-a))
    linarith
  obtain ⟨f,pos,chart,hit⟩ := h.budget
  refine ⟨max 1 (t*C),lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
  refine ⟨f,pos,chart,fun x=>budget_loosen (budget_mono (budget_scale tpos.le (hit x)) ?_ ?_)
    (le_max_right _ _)⟩
  · intro j
    split_ifs with hx
    · exact mul_nonneg (mul_nonneg (Poly.worth hp _).le (pos j)) (Real.exp_pos _).le
    · exact le_rfl
  · intro j
    by_cases hx:x∈L.ground j
    · simp only [if_pos hx]
      calc
        _ ≤ (Poly.toll w (L.mode j)*f j)*(t*Real.exp (a*coverNumber B (L.ground j))) :=
          mul_le_mul_of_nonneg_left (factor j) (mul_nonneg (Poly.worth hp _).le (pos j))
        _ = _ := by ring
    · simp only [if_neg hx, mul_zero, le_refl]
end YM.Integration.WilsonFiniteGalleryWidth
end
