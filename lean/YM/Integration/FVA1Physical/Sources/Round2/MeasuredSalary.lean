import YM.Integration.FVA1Physical.Sources.Round2.FieldUtopia

/-! Replacing just the observable in a positive normalized Haar integral is
1-Lipschitz. This keeps the actual source-Taylor error additive, independently
of the auxiliary allowances used to purchase the interacting-action expansion. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open MeasureTheory Set Filter Finset MSbar MSbar.Bakery MSbar.Bakery.Portal
open scoped Classical Topology BigOperators

/-- In a measured action expansion replace its bounded source by its literal
Taylor polynomial inside the same normalized conditional weight. The buying
allowance for the polynomial can be arbitrarily small independently of the cost
of replacing the real source. -/
theorem measured_salary {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (area : Set α) (Q H : α→PowerSeries ℝ) (f g d : α→ℝ) (p : ℕ)
    (t r a B c D b K X E : ℝ) (paid : Survey μ area Q H f g d p t r a B c D b K X)
    (alive : area.Nonempty) (budget : 0 ≤ E)
    (meas : Measurable (fun x=>taste p (H x) t)) :
    let P:=fun x=>taste p (H x) t;let ρ:=purse area g
    Survey μ area Q H P g d p t r a B c D b K E ∧
     |(∫ x,ρ x*f x ∂μ)/(∫ x,ρ x ∂μ) - (∫ x,ρ x*P x ∂μ)/(∫ x,ρ x ∂μ)| ≤ X := by
  intro P ρ
  have positive (x:α) : 0 ≤ ρ x:=Set.indicator_nonneg (fun _ _=>(Real.exp_pos _).le) x
  have inside (x:α) (hx:ρ x≠0) : x∈area:=by by_contra hn;exact hx (Set.indicator_of_notMem hn _)
  have safe (x:α) (hx:x∈area) : |P x| ≤ c:=(taste_pays paid.aura paid.young _).trans (paid.paid x hx).2
  have diff (x:α) (hx:x∈area) := (paid.bits x hx).2.2
  obtain ⟨y,hy⟩:=alive
  have lip : 0 ≤ X := (abs_nonneg _).trans (diff y hy)
  have integrable : Integrable (ρ*P) μ := by
    apply (paid.fullC.mul_const c).mono' (paid.fullC.aestronglyMeasurable.mul meas.aestronglyMeasurable)
    apply Filter.Eventually.of_forall;intro x
    change ‖ρ x*P x‖ ≤ ρ x*c
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (positive x)]
    by_cases z:ρ x=0
    · simp only [z,zero_mul,le_refl]
    exact mul_le_mul_of_nonneg_left (safe x (inside x z)) (positive x)
  refine ⟨{paid with markC:=integrable,rareT:=meas,bits:=fun x hx=>⟨(paid.bits x hx).1,
    (paid.bits x hx).2.1,by simpa only [P,sub_self,abs_zero] using budget⟩},?_⟩
  apply common_mass_sub μ ρ f P positive paid.rareT meas lip (M:=X+c)
  · intro x hx
    rw [←sub_add_cancel (f x) (P x)]
    exact (abs_add_le ..).trans (add_le_add (diff x (inside x hx)) (safe x (inside x hx)))
  exact fun x hx=>diff x (inside x hx)

end YM.Integration.FVA1Physical.Round2.Curvature
