import YM.Integration.WilsonRetainedJointVertexMoment

/-! A marked factor with its own Gaussian moment in a simultaneous retained-action estimate. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace YM.Integration.OriginalMarkedRunAction

/-- Put the marked insertion in the same Hölder product as the action slots.
The insertion has no Taylor error and can be unbounded. -/
theorem joined_marked_price {Ω I : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]
    (μ : Measure Ω) (a t : I → Ω → ℂ) (c e b : I → ℝ)
    (ma : ∀ i, AEStronglyMeasurable (a i) μ) (mt : ∀ i, AEStronglyMeasurable (t i) μ)
    (hc : ∀ i, 0 ≤ c i) (he : ∀ i, 0 ≤ e i)
    (actual : ∀ i, Integrable (fun z => ‖a i z‖^(Fintype.card I+1)) μ ∧
      ∫ z, ‖a i z‖^(Fintype.card I+1) ∂μ ≤ c i^(Fintype.card I+1))
    (error : ∀ i, Integrable (fun z => ‖t i z-a i z‖^(Fintype.card I+1)) μ ∧
      ∫ z, ‖t i z-a i z‖^(Fintype.card I+1) ∂μ ≤ e i^(Fintype.card I+1))
    {δ : ℝ} (d0 : 0 ≤ δ) (d1 : δ ≤ 1) (base : ∀ i, c i ≤ b i) (extra : ∀ i, e i ≤ δ*b i)
    (J : Ω → ℂ) (jm : AEStronglyMeasurable J μ) {B : ℝ} (hB : 0 ≤ B)
    (paid : Integrable (fun z => ‖J z‖^(Fintype.card I+1)) μ ∧
      ∫ z, ‖J z‖^(Fintype.card I+1) ∂μ ≤ B^(Fintype.card I+1)) :
    let defect := fun z => J z*((∏ i, t i z)-∏ i, a i z)
    Integrable defect μ ∧ ‖∫ z, defect z ∂μ‖ ≤ B*((2:ℝ)^(Fintype.card I+1)*δ*∏ i, b i) := by
  intro defect
  let old : Option I → Ω → ℂ := Option.elim' J a
  let new : Option I → Ω → ℂ := Option.elim' J t
  let ca : Option I → ℝ := Option.elim' B c
  let ce : Option I → ℝ := Option.elim' 0 e
  let cb : Option I → ℝ := Option.elim' B b
  have allA (u : Option I) : Integrable (fun z => ‖old u z‖^Fintype.card (Option I)) μ ∧
      ∫ z, ‖old u z‖^Fintype.card (Option I) ∂μ ≤ ca u^Fintype.card (Option I) := by
    cases u with
    | none => simpa only [old, ca, Option.elim'_none, Fintype.card_option] using paid
    | some i => simpa only [old, ca, Option.elim'_some, Fintype.card_option] using actual i
  have allE (u : Option I) : Integrable (fun z => ‖new u z-old u z‖^Fintype.card (Option I)) μ ∧
      ∫ z, ‖new u z-old u z‖^Fintype.card (Option I) ∂μ ≤ ce u^Fintype.card (Option I) := by
    cases u with
    | none => simp [old, new, ce]
    | some i => simpa only [old, new, ce, Option.elim'_some, Fintype.card_option] using error i
  obtain ⟨int, bound⟩ := joined_vertex_price μ old new ca ce cb
    (by rintro (_|u); exact jm; exact ma u) (by rintro (_|u); exact jm; exact mt u)
    (by rintro (_|u); exact hB; exact hc u) (by rintro (_|u); exact le_rfl; exact he u)
    allA allE d0 d1
    (by rintro (_|u); exact le_rfl; exact base u) (by rintro (_|u); exact mul_nonneg d0 hB; exact extra u)
    (fun _ => 1) aestronglyMeasurable_const zero_le_one (fun _ => by simp)
  have same (z : Ω) : (∏ u, new u z)-(∏ u, old u z) = defect z := by
    simp [Fintype.prod_option, new, old, defect, mul_sub]
  simp only [one_mul, same] at int bound
  simp only [Fintype.prod_option, cb, Option.elim'_none, Option.elim'_some] at bound
  refine ⟨int, bound.trans ?_⟩
  have count : ((Finset.univ : Finset (Finset (Option I))).erase ∅).card ≤ 2^(Fintype.card I+1) := by
    simp
  have cap : ((((Finset.univ : Finset (Finset (Option I))).erase ∅).card) : ℝ) ≤ (2:ℝ)^(Fintype.card I+1) := by
    exact_mod_cast count
  have total : 0 ≤ B*∏ i, b i := mul_nonneg hB (Finset.prod_nonneg fun i _ => (hc i).trans (base i))
  calc
    _ ≤ (2:ℝ)^(Fintype.card I+1)*δ*(B*∏ i, b i) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right cap d0) total
    _ = _ := by ring

end YM.Integration.OriginalMarkedRunAction

