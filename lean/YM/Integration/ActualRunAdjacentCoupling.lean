import YM.Integration.ActualRunBetaResetDomain

/-! Uniform comparison of the actual adjacent regulators of one Run.
The original half-radius event supplies the entire level and window tails;
no predicted beta, Plan equality, or additional trajectory estimate is used. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualRunAdjacentCoupling
open Filter PhysicalNext.Repeat.Legato Pert.Asymptotics
open MatchingLedger.Compass.Income

private theorem inv_sqrt_bounds {x : ℝ} (hx : |x| ≤ (1 / 2 : ℝ)) :
    (1 / 2 : ℝ) ≤ (Real.sqrt (1 - x))⁻¹ ∧
      (Real.sqrt (1 - x))⁻¹ ≤ 2 := by
  rcases abs_le.mp hx with ⟨hxlo, hxhi⟩
  have hp : 0 < 1 - x := by linarith
  have hslo : (1 / 2 : ℝ) ≤ Real.sqrt (1 - x) :=
    (Real.le_sqrt (by norm_num) hp.le).2 (by nlinarith only [hxhi])
  have hshi : Real.sqrt (1 - x) ≤ 2 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith only [hxlo]⟩
  have hpos := Real.sqrt_pos.mpr hp
  constructor
  · have h : (1 / 2 : ℝ) ≤ 1 / Real.sqrt (1 - x) :=
      (le_div_iff₀ hpos).2 (by nlinarith only [hshi])
    simpa only [one_div] using h
  · have h : 1 / Real.sqrt (1 - x) ≤ (2 : ℝ) :=
      (div_le_iff₀ hpos).2 (by nlinarith only [hslo])
    simpa only [one_div] using h

private theorem ratio_eq_inv_sqrt {G : Gauge} (R : Run G)
    (N p m : ℕ) (hm : m < N) :
    regulatorRun R.family N p (m + 1) / regulatorRun R.family N p m =
      (Real.sqrt (1 -
        (R.family.path.β N p m - R.family.path.β N p (m + 1)) *
          regulatorRun R.family N p m ^ 2))⁻¹ := by
  have hc := Weather.iceborn R.family R.makes hm.le p
  have hsq : regulatorRun R.family N p m ^ 2 =
      (R.family.path.β N p m)⁻¹ := by
    unfold regulatorRun
    rw [inv_pow, Real.sq_sqrt hc.le]
  have hr : 1 -
      (R.family.path.β N p m - R.family.path.β N p (m + 1)) *
        regulatorRun R.family N p m ^ 2 =
      R.family.path.β N p (m + 1) / R.family.path.β N p m := by
    calc
      _ = R.family.path.β N p m * regulatorRun R.family N p m ^ 2 -
          (R.family.path.β N p m - R.family.path.β N p (m + 1)) *
            regulatorRun R.family N p m ^ 2 := by
        rw [Weather.epoch R.family R.makes hm.le p]
      _ = R.family.path.β N p (m + 1) *
          regulatorRun R.family N p m ^ 2 := by ring
      _ = R.family.path.β N p (m + 1) *
          (R.family.path.β N p m)⁻¹ :=
        congrArg (fun t : ℝ => R.family.path.β N p (m + 1) * t) hsq
      _ = _ := (div_eq_mul_inv _ _).symm
  rw [hr]
  unfold regulatorRun
  rw [Real.sqrt_div' _ hc.le]
  simp only [inv_div']

/-- The same level event precedes every cutoff and physical period. -/
theorem eventually_ratio {G : Gauge} (R : Run G) (hG : G.Simple) :
    ∀ᶠ m : ℕ in atTop, ∀ N p : ℕ, m < N →
      (1 / 2 : ℝ) ≤
          regulatorRun R.family N p (m + 1) / regulatorRun R.family N p m ∧
        regulatorRun R.family N p (m + 1) / regulatorRun R.family N p m ≤ 2 := by
  filter_upwards [ActualRunBetaResetDomain.half_radius R hG] with m hm
  intro N p hN
  simpa only [ratio_eq_inv_sqrt R N p m hN] using
    inv_sqrt_bounds (hm N p hN)

/-- All levels above the original window's lower endpoint share the same
event, still before every cutoff and period. -/
theorem window_ratio {G : Gauge} (R : Run G) (hG : G.Simple)
    {ι : Type*} {l : Filter ι} (lower : ι → ℕ)
    (hlower : Tendsto lower l atTop) :
    ∀ᶠ a in l, ∀ m : ℕ, lower a ≤ m → ∀ N p : ℕ, m < N →
      (1 / 2 : ℝ) ≤
          regulatorRun R.family N p (m + 1) / regulatorRun R.family N p m ∧
        regulatorRun R.family N p (m + 1) / regulatorRun R.family N p m ≤ 2 := by
  filter_upwards [ActualRunBetaResetDomain.window_half_radius R hG lower hlower]
    with a ha
  intro m hm N p hN
  simpa only [ratio_eq_inv_sqrt R N p m hN] using
    inv_sqrt_bounds (ha m hm N p hN)

end YM.Integration.ActualRunAdjacentCoupling
end
