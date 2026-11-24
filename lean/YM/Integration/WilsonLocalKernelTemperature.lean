import YM.Integration.WilsonLocalKernelNormalization

/-! A finite change of temperature in the genuine normalized local Wilson kernel. -/
noncomputable section
namespace YM.Integration.WilsonLocalKernelTemperature
open YM RG RG02 RG02.Asym Lattice
open PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Tested
open Filter PowerSeries
open scoped Topology BigOperators

theorem rescaled_polynomial (P : PowerSeries ℂ) (r t : ℝ) (n : ℕ) :
    peval (fun i => coeff i (rescale (r : ℂ) P)) n t =
      peval (fun i => coeff i P) n (r*t) := by
  unfold peval Zone.eval
  apply Finset.sum_congr rfl
  intro i _
  simp only [coeff_rescale, Complex.real_smul, Complex.ofReal_pow, Complex.ofReal_mul, mul_pow]
  ring

theorem dilation {x : ℝ → ℂ} {P : PowerSeries ℂ} {r : ℝ} (hr : 0 < r) (h : Near x P) :
    Near (fun t => x (r*t)) (rescale (r : ℂ) P) := by
  have hc : Tendsto (fun t : ℝ => r*t) (𝓝 0) (𝓝 (r*0)) :=
    tendsto_const_nhds.mul tendsto_id
  rw [mul_zero] at hc
  have hd : Tendsto (fun t : ℝ => r*t) Tested.germ Tested.germ :=
    tendsto_nhdsWithin_iff.mpr ⟨hc.mono_left nhdsWithin_le_nhds,
      Tested.eventually_pos.mono fun _ ht => mul_pos hr ht⟩
  intro n
  obtain ⟨C,hC,H⟩ := h n
  refine ⟨C*r^(n+1), mul_nonneg hC (pow_nonneg hr.le _), (hd.eventually H).mono ?_⟩
  intro t ht
  change ‖x (r*t) - peval (fun i => coeff i (rescale (r : ℂ) P)) n t‖ ≤ _
  rw [rescaled_polynomial]
  simpa only [Pi.sub_apply, mul_pow, mul_assoc] using ht

variable {c f : Side} (S : StepData c f)

def series (G : Gauge) (r : ℝ) : PowerSeries ℂ :=
  let P := Friction.paidSeries S (XSpace.Bare.chart G)
  C ((r : ℂ)^(Friction.cardinal G)) * rescale (r : ℂ) P * P⁻¹

def ratio (G : Gauge) (r t : ℝ) : ℂ :=
  (S.penaltyZ ((r*t)^2)⁻¹ G : ℂ) / (S.penaltyZ (t^2)⁻¹ G : ℂ)

theorem all_orders (G : Gauge) {r : ℝ} (hr : 0 < r) :
    Near (ratio S G r) (series S G r) := by
  let η := XSpace.Bare.chart G
  have hη := XSpace.Bare.chart_ratio G
  have h := Friction.restored S η hη
  have hz : coeff 0 (Friction.paidSeries S η) ≠ 0 := by
    rw [Friction.paid_base S η hη]
    exact Complex.ofReal_ne_zero.mpr (mul_pos (Therm.leading_pos ..) hη.scale).ne'
  have H := Near.mult (Near.mult (Near.fixed ((r : ℂ)^(Friction.cardinal G))) (dilation hr h)) (Near.fine_inverse h hz)
  apply Near.same H
  filter_upwards [Tested.eventually_pos] with t ht
  change (r : ℂ)^(Friction.cardinal G) *
      (((((r*t : ℝ) : ℂ)^(Friction.cardinal G))⁻¹) * ↑(S.penaltyZ ((r*t)^2)⁻¹ G)) *
      (((((t : ℂ)^(Friction.cardinal G))⁻¹) * ↑(S.penaltyZ (t^2)⁻¹ G))⁻¹) = _
  unfold ratio
  have hrC := Complex.ofReal_ne_zero.mpr hr.ne'
  have htC := Complex.ofReal_ne_zero.mpr ht.ne'
  have hzC := Complex.ofReal_ne_zero.mpr (S.penaltyZ_pos (G:=G) (t^2)⁻¹).ne'
  rw [Complex.ofReal_mul, mul_pow]
  field_simp [hrC, htC, hzC]

/-- The leading normalized link-price transform is the Euclidean Gaussian
temperature ratio in the actual Lie algebra dimension. -/
theorem leading (G : Gauge) (r : ℝ) : coeff 0 (series S G r) = (r : ℂ)^(Friction.cardinal G) := by
  let P := Friction.paidSeries S (XSpace.Bare.chart G)
  have hη := XSpace.Bare.chart_ratio G
  have hz : coeff 0 P ≠ 0 := by
    dsimp only [P]
    rw [Friction.paid_base S _ hη]
    exact Complex.ofReal_ne_zero.mpr (mul_pos (Therm.leading_pos ..) hη.scale).ne'
  change coeff 0 (C ((r : ℂ)^_) * rescale (r : ℂ) P * P⁻¹) = _
  have hres : constantCoeff (rescale (r : ℂ) P) = coeff 0 P := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale, pow_zero, one_mul]
  have hp : constantCoeff P = coeff 0 P := (coeff_zero_eq_constantCoeff_apply P).symm
  rw [coeff_zero_eq_constantCoeff_apply, map_mul, map_mul, constantCoeff_inv,
    constantCoeff_C, hres, hp, mul_assoc, mul_inv_cancel₀ hz, mul_one]

end YM.Integration.WilsonLocalKernelTemperature
