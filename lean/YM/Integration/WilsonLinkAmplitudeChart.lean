import YM.Integration.WilsonLocalKernelNormalization

/-! A signed smooth test amplitude in the measured one-link Haar integral. -/
noncomputable section
namespace YM.Integration.WilsonLinkAmplitudeChart
open YM RG RG02 Lattice Wilson Filter Function MeasureTheory Set Metric Precision
open PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Tested RG02.Asym RG02.Therm
open PertExtension.Series.Radial
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {c f : Side} (S : StepData c f)

def weighted (a : Friction.W G → ℝ) (t : ℝ) (x : Friction.W G) :=
  Friction.life S t x * a x

def amplitude (P : ChartRatio G) (a : Friction.W G → ℝ) (x : ℝ × Friction.E G) : ℂ :=
  Friction.jac P x * (a (expLinks G Unit x.2) : ℂ)

theorem inner (P : ChartRatio G) (hP : LocalRatio P) (a : Friction.W G → ℝ)
    (ha : Continuous a) {t r : ℝ} (ht : 0<t) (hr : 0<r) (hs : r < Chart.small G P) :
    ((t:ℂ)^Friction.cardinal G)⁻¹ * Complex.ofReal
      (∫ x in chamber G Unit r, weighted S a t x ∂Friction.roll G) =
      ∫ u in disc t r, Therm.sheet (Friction.hinge S) (amplitude P a) t u ∂Friction.rate G := by
  let w (u : Friction.E G) := Chart.jacobian P u * weighted S a t (expLinks G Unit u)
  rw [Chart.Ratio.chamber_integral hP (weighted S a t) ((Friction.line S t).mul ha).measurable hs hr]
  change ((t:ℂ)^_)⁻¹ * ↑(∫ x in Metric.ball 0 r, w x ∂Friction.rate G) = _
  let A := Metric.ball (0 : Friction.E G) r
  let B := disc (E:=Friction.E G) t r
  have h0 (u : Friction.E G) : Therm.sheet (Friction.hinge S) (Friction.jac P) t u =
      Complex.ofReal (Chart.jacobian P (t • u)*Friction.life S t (expLinks G Unit (t • u))) := by
    unfold Therm.sheet Therm.turbine Friction.hinge Friction.life StepData.penaltyWeight
      Friction.jac Friction.jetBase
    dsimp only [expLinks]
    push_cast
    congr 3
    field_simp
  have he (u : Friction.E G) :
      Therm.sheet (Friction.hinge S) (amplitude P a) t u = Complex.ofReal (w (t • u)) := by
    calc _ = Therm.sheet (Friction.hinge S) (Friction.jac P) t u *
          ↑(a (expLinks G Unit (t • u))) := by simp only [Therm.sheet,amplitude]; ring
         _ = _ := by rw [h0]; dsimp only [w,weighted]; push_cast; ring
  simp_rw [he]
  symm
  refine (integral_ofReal (𝕜:=ℂ) (μ:=(Friction.rate G).restrict (disc t r))
    (f:=fun x => w (t • x))).trans ?_
  symm
  have hg := Measure.integral_comp_smul_of_nonneg (Friction.rate G) (A.indicator w) t (hR:=ht.le)
  have hh x : A.indicator w (t • x) = B.indicator (fun u : Friction.E G => w (t • u)) x := by
    by_cases h : x ∈ B
    · rw [indicator_of_mem (s:=A) (show t • x ∈ A from h),indicator_of_mem h]
    rw [indicator_of_notMem (s:=A) (show t • x ∉ A from h),indicator_of_notMem h]
  simp_rw [hh] at hg
  rw [integral_indicator (s:=A) isOpen_ball.measurableSet,integral_indicator (s:=B) (disc_meas ..)] at hg
  change _ = Complex.ofReal (∫ u in B, w (t • u) ∂Friction.rate G)
  rw [hg,smul_eq_mul]
  push_cast
  rfl

theorem outer (P : ChartRatio G) (hP : LocalRatio P) (a : Friction.W G → ℝ)
    (ha : Continuous a) {r : ℝ} (hr : 0<r) (hs : r < Chart.small G P) (n : ℕ) :
    Bill n (fun t => ((t:ℂ)^Friction.cardinal G)⁻¹ * Complex.ofReal
      (∫ x in (chamber G Unit r)ᶜ, weighted S a t x ∂Friction.roll G)) := by
  obtain ⟨M,hM⟩ := isCompact_univ.exists_bound_of_continuousOn ha.continuousOn
  have hM0 : 0≤M := (norm_nonneg (a (fun _ => 1))).trans (hM _ (Set.mem_univ _))
  obtain ⟨D,hD,h⟩ := Friction.outer S P hP hr hs n
  refine ⟨M*D,mul_nonneg hM0 hD,?_⟩
  filter_upwards [h] with t ht
  let A := (chamber G Unit r)ᶜ
  let z := ((t:ℂ)^Friction.cardinal G)⁻¹
  have hl (x : Friction.W G) : 0 ≤ Friction.life S t x := (Real.exp_pos _).le
  have hi : IntegrableOn (Friction.life S t) A (Friction.roll G) :=
    ((Friction.line S t).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).integrableOn
  have hb : ‖∫ x in A, weighted S a t x ∂Friction.roll G‖ ≤ M * ∫ x in A, Friction.life S t x ∂Friction.roll G := by
    rw [←integral_const_mul]
    apply norm_integral_le_of_norm_le (hi.const_mul M)
    apply ae_of_all
    intro x
    rw [weighted,norm_mul,Real.norm_of_nonneg (hl x),mul_comm M]
    exact mul_le_mul_of_nonneg_left (hM x (Set.mem_univ _)) (hl x)
  change ‖z*Complex.ofReal (∫ x in A, weighted S a t x ∂Friction.roll G)‖ ≤ (M*D)*t^n
  calc _ = ‖z‖*‖∫ x in A, weighted S a t x ∂Friction.roll G‖ := by rw [norm_mul,Complex.norm_real]
       _ ≤ ‖z‖*(M*∫ x in A, Friction.life S t x ∂Friction.roll G) :=
          mul_le_mul_of_nonneg_left hb (norm_nonneg _)
       _ = M*‖z*Complex.ofReal (∫ x in A, Friction.life S t x ∂Friction.roll G)‖ := by
         rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (integral_nonneg hl)]; ring
       _ ≤ _ := (mul_le_mul_of_nonneg_left ht hM0).trans_eq (by ring)

end YM.Integration.WilsonLinkAmplitudeChart
