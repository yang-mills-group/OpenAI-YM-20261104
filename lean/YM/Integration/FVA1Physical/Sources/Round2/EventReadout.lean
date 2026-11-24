import YM.Integration.FVA1Physical.Sources.Round2.PhysicalReadout

/-! Conditional joint readout on any measurable event of coarse fields. -/

namespace YM.Integration.FVA1Physical.Round2

open Filter MeasureTheory Lattice RG Wilson

theorem eventReadout {G : Gauge} {H : History G} {N n i : ℕ} (hH : H.Selected)
    (hi : i ≤ N) (e : Set (Config G (H.S.side i n))) (he : MeasurableSet e)
    (f : Config G (H.S.side i n) → ℂ) {C : ℝ}
    (hfm : AEStronglyMeasurable f (prior G (H.S.side i n)))
    (hf : ∀ v, ‖f v‖ ≤ (H.rep N n i).eval v * C) :
    IntegrableOn f e (prior G (H.S.side i n)) ∧
      (∫ v in e, ‖f v‖ ∂prior G (H.S.side i n)) /
        partition G (H.S.side N n) (H.β N n N) ≤ C * (OPE.Therm.scene H N n i).real e := by
  let μ := prior G (H.S.side i n)
  let ν := OPE.Therm.scene H N n i
  let Z := partition G (H.S.side N n) (H.β N n N)
  let w := (H.rep N n i).eval
  haveI : IsProbabilityMeasure ν := OPE.Therm.probability hH hi
  have hw : Integrable w μ := ((H.rep N n i).envelope (hH.represents N n i hi).good).integrable _
  have hmaj : Integrable (fun v => w v * C) (μ.restrict e) := hw.restrict.mul_const C
  have hb : ∀ᵐ v ∂(μ.restrict e), ‖f v‖ ≤ w v * C := Eventually.of_forall hf
  have hint := hmaj.mono' hfm.restrict hb
  refine ⟨hint, ?_⟩
  have area : (∫ v in e, w v ∂μ) / Z = ν.real e := by
    let χ := e.indicator (fun _ => (1 : ℝ))
    have hχ : (∫ v, χ v ∂ν) = ν.real e := by simp [χ, integral_indicator he, measureReal_def]
    rw [OPE.Therm.scenery hH hi χ] at hχ
    have hh : (fun v => w v * χ v) = e.indicator w := by
      funext v
      by_cases hv : v ∈ e <;> simp [χ, hv]
    change (∫ v, w v * χ v ∂μ) / Z = ν.real e at hχ
    rwa [hh, integral_indicator he] at hχ
  have hZ : 0 < Z := partition_pos _
  have h := div_le_div_of_nonneg_right (integral_mono_ae hint.norm hmaj hb) hZ.le
  rw [integral_mul_const] at h
  change (∫ v in e, ‖f v‖ ∂μ) / Z ≤ C * ν.real e
  exact h.trans_eq (by rw [← area]; ring)

end YM.Integration.FVA1Physical.Round2
