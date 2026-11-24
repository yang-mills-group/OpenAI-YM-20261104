import YM.Integration.FullQLocalNumericSchedule

/-!
The existing numerical geometry bill pays fixed logarithmic native costs.
Both adjacent monitors already occur in that bill. Their exact formula
dominates every fixed power of log(hatBeta), with every fixed coefficient,
on one tail before any cutoff, period, selected model or test.

This does not compare a stage-dependent output geometry bill with the next
input budget, and does not identify any native coefficient or kernel price.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.FullQLocal.RenderedStep
open Filter Lattice Wilson RG
open scoped Topology

variable {G : Gauge} {V : Type} {C : Family G} {J : Request V}

private theorem beta_tendsto (D : Levels G) (hG : G.Simple) :
    Tendsto D.clock.hatBeta atTop atTop :=
  tendsto_atTop_add_const_left _ _
    (D.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos hG))

private theorem log_power_monitor (D : Levels G) (hG : G.Simple) (v : ℝ) :
    ∀ᶠ m : ℕ in atTop,
      Real.log (D.clock.hatBeta m) ^ v ≤ D.clock.monitor m := by
  have ht := Real.tendsto_log_atTop.comp
    (Real.tendsto_log_atTop.comp (beta_tendsto D hG))
  filter_upwards [ht.eventually_ge_atTop (max 0 v)] with m hm
  let x := Real.log (Real.log (D.clock.hatBeta m))
  change max 0 v ≤ x at hm
  rw [Real.rpow_def_of_pos (Real.log_pos (D.fits.delayed m))]
  change Real.exp (x * v) ≤ Real.exp (x ^ 2)
  apply Real.exp_monotone
  have hx : 0 ≤ x := (le_max_left 0 v).trans hm
  have hv : v ≤ x := (le_max_right 0 v).trans hm
  nlinarith only [mul_le_mul_of_nonneg_left hv hx]

private theorem constant_log_power_monitor
    (D : Levels G) (hG : G.Simple) (coefficient : ℝ) (k : ℕ) :
    ∀ᶠ m : ℕ in atTop,
      coefficient * Real.log (D.clock.hatBeta m) ^ k ≤ D.clock.monitor m := by
  have ht := Real.tendsto_log_atTop.comp (beta_tendsto D hG)
  filter_upwards [log_power_monitor D hG ((k + 1 : ℕ) : ℝ),
    ht.eventually_ge_atTop coefficient] with m hp hc
  have hpow : Real.log (D.clock.hatBeta m) ^ (k + 1) ≤ D.clock.monitor m := by
    simpa only [Real.rpow_natCast] using hp
  calc
    _ ≤ Real.log (D.clock.hatBeta m) *
        Real.log (D.clock.hatBeta m) ^ k :=
      mul_le_mul_of_nonneg_right hc
        (pow_nonneg (Real.log_pos (D.fits.delayed m)).le k)
    _ = Real.log (D.clock.hatBeta m) ^ (k + 1) := by
      rw [pow_succ]
      ring
    _ ≤ _ := hpow

/-- The complete geometry bill contains both adjacent monitors. -/
theorem NumericSchedule.monitor_cost (A : NumericSchedule C J) (m : ℕ) :
    C.path.levels.clock.monitor m + C.path.levels.clock.monitor (m + 1) ≤
      A.admittedCost m := by
  let D := C.path.levels
  change D.clock.monitor m + D.clock.monitor (m + 1) ≤ A.admittedCost m
  have hloop (k : ℕ) : 0 ≤ D.clock.loopCap k := by
    change 0 ≤ 2 * (D.clock.monitor k) ^ (D.clock.theta (D.clock.J k))
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg (Real.exp_nonneg _) _)
  have hcover0 : 0 ≤ (D.clock.coverSize m : ℝ) := Nat.cast_nonneg _
  have hcover1 : 0 ≤ (D.clock.coverSize (m + 1) : ℝ) := Nat.cast_nonneg _
  have hpath0 := (D.params m).paths_pos
  have hpath1 := (D.params (m + 1)).paths_pos
  have hcolumn0 := (D.params m).columns_ge
  have hcolumn1 := (D.params (m + 1)).columns_ge
  have hrelax0 := (D.params m).clip.radius_pos
  have hrelax1 := (D.params (m + 1)).clip.radius_pos
  have hbill := A.cost_covers_geometry m
  change 1 + (D.clock.coverSize m : ℝ) + (D.clock.coverSize (m + 1) : ℝ) +
    D.clock.monitor m + D.clock.monitor (m + 1) +
    D.clock.loopCap m + D.clock.loopCap (m + 1) +
    (D.params m).paths + (D.params (m + 1)).paths +
    (D.params m).columns + (D.params (m + 1)).columns +
    (D.params m).clip.relaxation + (D.params (m + 1)).clip.relaxation ≤
      A.admittedCost m at hbill
  linarith [hloop m, hloop (m + 1)]

/-- Every fixed logarithmic cost at both adjacent stages is paid on one tail.
The coefficient may be any real number; no new numerical premise is added. -/
theorem NumericSchedule.logarithmic_cost
    (A : NumericSchedule C J) (hG : G.Simple) (coefficient : ℝ) (k : ℕ) :
    ∀ᶠ m : ℕ in atTop,
      coefficient * Real.log (C.path.levels.clock.hatBeta m) ^ k +
        coefficient * Real.log (C.path.levels.clock.hatBeta (m + 1)) ^ k ≤
      A.admittedCost m := by
  have hp := constant_log_power_monitor C.path.levels hG coefficient k
  have hs := (tendsto_add_atTop_nat 1).eventually hp
  filter_upwards [hp, hs] with m hm hs
  exact (add_le_add hm hs).trans (A.monitor_cost m)

end YM.Integration.FullQLocal.RenderedStep
end
