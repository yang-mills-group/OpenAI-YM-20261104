import YM.Integration.FVA1Physical.CommonCover.CurvatureDampedWilson

/-! A gauge-invariant curvature collar and one penalty for a whole family of
held tests. Only the auxiliary Wilson continuation is modified. Its formal
coefficients at every order are fixed. The size of the original physical tail
still needs to be bounded on the unmodified true law. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.OlderPrice
open Filter Function Set MeasureTheory RG Wilson Gauge Precision Tree Lattice Exterior
open Comparison.RG02 Order Marker Multi Integral Actual
open scoped Classical Topology BigOperators Matrix.Norms.Frobenius

variable {I : Type} [DecidableEq I] [Fintype I] {R : Census I} {G : Gauge} {c f : Side}
variable {S : StepData c f} {p : Clip} {P : PathData G} {O : ChartRatio G}

def curvatureCollar (D : BudgetPoint) (σ : Support f) : Set (Config G f) :=
  {U | Healthy D.threshold σ U}

theorem collar_geometry (D : BudgetPoint) (σ : Support f) :
    curvatureCollar (G:=G) D σ ∈ 𝓝 (1 : Config G f) ∧
    MeasurableSet (curvatureCollar (G:=G) D σ) ∧
    ∀ k U, Lattice.gauge k U ∈ curvatureCollar D σ ↔ U ∈ curvatureCollar (G:=G) D σ := by
  refine ⟨?_,(healthy_closed D.threshold σ).measurableSet,?_⟩
  · filter_upwards [calm_germ (G:=G) (f:=f) D] with U h
    change flags D.threshold U=∅ at h
    change Disjoint σ (flags D.threshold U)
    simp [h]
  · intro k U
    change Disjoint σ (flags D.threshold (Lattice.gauge k U)) ↔ Disjoint σ (flags D.threshold U)
    rw [gauge_flags]

theorem curvature_collar_wilson (K : Bulk.Kernel S p P O) (F : Forest S.ratio) (t : S.Choices)
    (W : Bulk.Colors R G f) (well : Bulk.Well W) (D : BudgetPoint) (σ : Support f) (d : ℝ→ℝ) :
    Bulk.Well (dampedWilson W (curvatureCollar D σ) d) ∧
    ∀ (x:fieldDir G c 1) (m:ℕ), Bulk.Fk K F t (dampedWilson W (curvatureCollar D σ) d) x m=
      Bulk.Fk K F t W x m := by
  obtain ⟨an,am,ag⟩:=collar_geometry (G:=G) D σ
  exact ⟨damped_wilson_well W well _ an am ag d, fun x m=>damped_wilson_coefficients K F t W _ an d x m⟩

omit [Fintype I] in
/-- One unnormalized majorant across all held tests buys any prescribed
positive auxiliary-model allowance outside the unchanged curvature collar. -/
theorem failed_model_budget {Ω T : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (U : Ω → Config G f) (um : Measurable U) (D : BudgetPoint) (σ : Support f)
    (W : Bulk.Colors R G f) (g c₀ : ℝ) (hg:g≠0) (tests:T → Ω → ℝ) (B ε:ℝ)
    (hp:0≤B) (he:0<ε)
    (cost:∀i, (∫ y in U ⁻¹' (curvatureCollar D σ)ᶜ,
       (tests i y) * weight g c₀ (U y) W p P ∂μ) ≤ B) :
    ∃ d:ℝ→ℝ, (∀h,0≤d h) ∧ ∀ i, (∫ y in U ⁻¹' (curvatureCollar D σ)ᶜ,
        (tests i y) * weight g c₀ (U y) (dampedWilson W (curvatureCollar D σ) d) p P ∂μ) ≤ ε := by
  let d : ℝ→ℝ := fun _=>Real.log (1+B/ε)
  have one : 1≤1+B/ε := by linarith [div_nonneg hp he.le]
  have plus : 0<1+B/ε:=lt_of_lt_of_le zero_lt_one one
  refine ⟨d,fun _=>Real.log_nonneg one,?_⟩
  intro i
  let bad := U ⁻¹' (curvatureCollar D σ)ᶜ
  have bm : MeasurableSet bad := um (collar_geometry (G:=G) D σ).2.1.compl
  calc
    _ = ∫ y in bad, Real.exp (-d g)*((tests i y)*weight g c₀ (U y) W p P) ∂μ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem bm] with y hy
      have hy' : U y∉curvatureCollar D σ := hy
      rw [damped_wilson_weight W _ d g c₀ hg, if_neg hy']
      ring
    _ = Real.exp (-d g)*(∫ y in bad, (tests i y)*weight g c₀ (U y) W p P ∂μ) := integral_const_mul ..
    _ ≤ Real.exp (-d g)*B := mul_le_mul_of_nonneg_left (cost i) (Real.exp_pos _).le
    _ ≤ ε := by
      change Real.exp (-Real.log (1+B/ε))*B ≤ ε
      rw [Real.exp_neg, Real.exp_log plus, ← div_eq_inv_mul]
      apply (div_le_iff₀ plus).mpr
      have cancel : ε*(B/ε)=B := by field_simp
      rw [mul_add, mul_one, cancel]
      linarith
end YM.Integration.FVA1Physical.OlderPrice
