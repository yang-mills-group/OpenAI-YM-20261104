import YM.Integration.FVA1Physical.Sources.Round2.StencilWickChart

/-! Absolute logarithm coordinates of the actual draw are uniformly small throughout
the support of the inherited Wilson angular measure. No relative error at the
vacuum denominator is required to replace the inserted stencil in that measure. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1700000
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Function Filter Set Finset MeasureTheory Lattice RG YM.Wilson Tree Precision Exterior Pressure
open RGComparison.Core16 RGComparison.Core16.Spool RGComparison.Core16.Lumen
open MSbar MSbar.Heath MSbar.Heath.Cottage MSbar.Heath.Stock MSbar.Bakery MSbar.Bakery.Film
open MSbar.Cacao MSbar.Whisk Push.Uniform Next.SectorChange YM.Integration.FVA1Physical.Wilson
open scoped Classical Topology BigOperators
variable {G : Gauge} {c f : Side} {S : StepData c f} (F : Forest S.ratio)

theorem drawn_log_cap (J : Voice G) (X Y : Support f) (O : Config G c) (V : Config G f)
    (ν : Positions (Key F G)) (γ : ChartRatio G) (hγ : LocalRatio γ) (clear : Clear G J)
    (v : F.Free → G.Color) {a b K H M g : ℝ}
    (paid : Couch J F ν Y γ v O a b K H M) (xy : X⊆Y) (m w : SpaceP F X G)
    (within : w∈clipM F X Y (hotel F X Y J O ν a b) γ g m V) (e : ↥(board F X)) :
    ‖tape (m+g•w) e‖ ≤ 3*shade G*K := by
  let N:=draw F X V m g w
  let u:=rented F Y J O ν N
  let A:=imageNear J F (chambers F Y J O ν N)
  have anchor := (anchors J F X Y O ν γ clear v paid xy N within.1).2 e.val
  have chartEq := telling J F X Y O V m ν γ hγ clear v paid xy w within e
  have eu : ‖u‖≤K := by
    rw [show u=u-ν+ν from (sub_add_cancel u ν).symm]
    exact (norm_add_le (u-ν) ν).trans ((add_le_add
      (leanOn F X Y J O ν clear xy within.1 paid.lifts (paid.glued.le.trans paid.lifts)) le_rfl).trans ((add_comm ..).trans_le paid.ht))
  have bound : ‖tint G _ u e.val‖ ≤ shade G*K :=
    (norm_le_pi_norm (tint G _ u) e.val).trans ((tint_le u).trans (mul_le_mul_of_nonneg_left eu (shade_pos G).le))
  let l:=tint G _ A e.val
  let t:=tint G _ u e.val
  have both : ‖l-t-v e.val‖≤M := anchor.2
  rw [←chartEq]
  change ‖l‖≤_
  calc
    _=‖(l-t-v e.val)+t+v e.val‖ := by congr 1;abel
    _≤(M+shade G*K)+shade G*K := (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add both bound)) (paid.sums _))
    _≤_ :=by linarith only [paid.final]

/-- This tilted ratio uses the common *entire* nonnegative density, including its
Haar and action factors. Actual and approximate observables are bounded only on
the contributing set. -/
theorem common_mass_sub {X : Type*} [MeasurableSpace X] (μ : Measure X) (ρ F P : X→ℝ)
    (positive : ∀ x,0≤ρ x) (hF : Measurable F) (hP : Measurable P)
    {M ε : ℝ} (hε : 0≤ε)
    (fixed : ∀ x,ρ x≠0 → |F x|≤M) (err : ∀ x,ρ x≠0 → |F x-P x|≤ε) :
    |(∫ x,ρ x*F x ∂μ)/(∫ x,ρ x ∂μ)-(∫ x,ρ x*P x ∂μ)/(∫ x,ρ x ∂μ)| ≤ ε := by
  let m:=∫ x,ρ x ∂μ
  by_cases empty : m=0
  · change |_/m-_/m|≤_;rw [empty,div_zero,div_zero,sub_zero,abs_zero];exact hε
  have den : Integrable ρ μ:=by_contra (fun h=>empty (integral_undef h))
  have hm : 0 < m := lt_of_le_of_ne (MeasureTheory.integral_nonneg positive) (Ne.symm empty)
  have integ (φ : X→ℝ) (meas : Measurable φ) (t:ℝ) (h : ∀ x,ρ x≠0→|φ x|≤t) :
      Integrable (fun x=>ρ x*φ x) μ := by
    apply (den.mul_const t).mono' (den.aestronglyMeasurable.mul meas.aestronglyMeasurable)
    apply Filter.Eventually.of_forall;intro x
    by_cases hx:ρ x=0
    · simp [hx]
    change ‖ρ x*φ x‖ ≤ ρ x*t
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (positive x)]
    exact mul_le_mul_of_nonneg_left (h x hx) (positive x)
  have iF:=integ F hF M fixed
  have iP:=integ P hP (M+ε) (fun x hx=>by
    rw [←sub_sub_self (F x) (P x)];exact (abs_sub ..).trans (add_le_add (fixed x hx) (err x hx)))
  rw [←sub_div,←integral_sub iF iP,abs_div,abs_of_pos hm]
  apply (div_le_iff₀ hm).mpr
  calc
    _≤∫ x, ‖ρ x*F x-ρ x*P x‖ ∂μ := norm_integral_le_integral_norm _
    _≤∫ x,ρ x*ε ∂μ := integral_mono (iF.sub iP).norm (den.mul_const _) (fun x=>by
          by_cases hx:ρ x=0
          · simp [hx]
          rw [←mul_sub,Real.norm_eq_abs,abs_mul,abs_of_nonneg (positive x)]
          exact mul_le_mul_of_nonneg_left (err x hx) (positive x))
    _= ε*(∫ x,ρ x ∂μ) := by rw [integral_mul_const,mul_comm]

end YM.Integration.FVA1Physical.Round2.Curvature
