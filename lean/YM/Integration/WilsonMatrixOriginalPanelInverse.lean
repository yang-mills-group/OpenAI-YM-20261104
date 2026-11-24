import YM.Integration.WilsonGaussianOrientedPanel

/-! Inversion on the actual real line of test packets in the first measured Wilson row. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalPanelInverse
open Filter Function Table Spec Lattice Wilson RG RG17 Climb PhysMS Trace.Pilot
open PhysicalNext.Repeat.Legato SharpGram.Lenses
open Next.UVStress Extraction Extraction.Order Push.GridApprox OPE OPE.Therm
open WilsonMatrixOriginalFiledPanel WilsonMatrixOriginalOrientedPanel WilsonInvariantActionPairCovariance
open scoped Classical Topology BigOperators
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    (F : Final R.family f S) (L : Layout F)

/-- The actual finite positive-law covariance responds linearly to the submitted real packet. -/
theorem sample (a b : ℝ → R.family.label 4) (χ : ℂ →L[ℝ] ℝ) (φ : Test 2)
    {r : ℝ} (hr : 0 < r) (uv : ℕ × ℕ) (t : ℝ) :
    Value F L a b χ ((t : ℂ) • φ) hr uv = t * Value F L a b χ φ hr uv := by
  have point (x : Points 2) :
      (dilate hr ((t : ℂ) • φ) x).re = t * (dilate hr φ x).re := by
    have whole : dilate hr ((t : ℂ) • φ) x = (t : ℂ) * dilate hr φ x := by
      change (((r^(4*2))⁻¹ : ℝ) : ℂ) * ((t : ℂ) * φ (r⁻¹ • x)) =
        (t : ℂ) * ((((r^(4*2))⁻¹ : ℝ) : ℂ) * φ (r⁻¹ • x))
      ring
    rw [whole,Complex.mul_re]
    simp
  unfold Value WilsonMatrixOriginalSignedReading.signed
  simp_rw [point,mul_assoc t]
  rw [←Finset.mul_sum]
  ring

/-- One common bound and one orientation work for every real signal and additive readout error. -/
theorem recover {J : ℝ → tower S} {U : Filter (ℕ × ℕ)} {a b : ℝ → R.family.label 4}
    {v : ℝ → S.Field 4} {φ : Test 2} {c : ℂ} {χ : ℂ →L[ℝ] ℝ}
    (seen : WilsonMatrixOriginalOrientedPanel.Signed (U:=U) F J L a b v φ c χ) :
    ∃ (s K : ℝ), (s=1 ∨ s= -1) ∧ 0<s*χ c ∧ K=4/|χ c| ∧ 0<K ∧
      ∀ᶠ r in trail, ∀ hr : 0<r,
        let signal := fun (t : ℝ) (uv : ℕ × ℕ) => s * Value F L a b χ ((t : ℂ) • φ) hr uv
        let limit := s * χ (tested (J r 4 (stepField R.family)) (v r) r φ)
        Tendsto (fun uv => (s*Value F L a b χ φ hr uv)⁻¹) U (𝓝 limit⁻¹) ∧
          ∀ᶠ uv in U, ∃ decode : ℝ, 0 < decode ∧ decode < K ∧
            (∀ t : ℝ, decode * signal t uv = t) ∧
            (∀ t noise : ℝ, |decode * (signal t uv + noise) - t| ≤ K * |noise|) := by
  obtain ⟨nz,s,unit,orient,panel⟩ := seen
  refine ⟨s,4/|χ c|,unit,orient.symm ▸ nz,rfl,by positivity,?_⟩
  filter_upwards [panel] with r at_r
  intro hr
  obtain ⟨half,readings,quarters⟩ := at_r hr
  have pos : 0 < s*χ (tested (J r 4 (stepField R.family)) (v r) r φ) :=
    lt_trans (div_pos nz (by norm_num)) half
  refine ⟨readings.inv₀ pos.ne',?_⟩
  filter_upwards [quarters] with uv big
  let h := s * Value F L a b χ φ hr uv
  have hp : 0 < h := lt_trans (div_pos nz (by norm_num)) big
  have bound : h⁻¹ < 4/|χ c| := by
    rw [inv_eq_one_div,div_lt_div_iff₀ hp nz]
    change |χ c|/4 < h at big
    linarith
  have exact_signal (t : ℝ) : h⁻¹*(s*Value F L a b χ ((t:ℂ) • φ) hr uv) = t := by
    rw [sample]
    calc
      _ = (h⁻¹*h)*t := by dsimp [h]; ring
      _ = t := by rw [inv_mul_cancel₀ hp.ne',one_mul]
  refine ⟨h⁻¹,inv_pos.mpr hp,bound,exact_signal,?_⟩
  intro t noise
  rw [mul_add,exact_signal]
  simp only [add_sub_cancel_left,abs_mul,abs_of_pos (inv_pos.mpr hp)]
  exact mul_le_mul_of_nonneg_right bound.le (abs_nonneg noise)

end YM.Integration.WilsonMatrixOriginalPanelInverse
end
