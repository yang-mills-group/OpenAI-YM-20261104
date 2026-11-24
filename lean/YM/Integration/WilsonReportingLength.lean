import YM.OPE.Log.Grid
import YM.PhysMS.Foundation.Estimates

/-! The genuine numerical reporting radius and the location of its lattice
stage between the coarse capture and the original fine field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingLength
open Filter Function Lattice RG Wilson MergeProof OPE Trace.Pilot
open scoped Topology
variable {G : Gauge} (C : Family G)

/-- The manuscript's positive logarithmic measuring unit on this family. -/
def unit (m : ℕ) : ℝ := 2 + Real.log (C.path.levels.clock.hatBeta m)

/-- The physical separation is a prescribed power of the measuring unit
times the original spacing, with no change to the regulated family. -/
def radius (B : ℝ) (m : ℕ) : ℝ := C.S.a m * (unit C m)^B

theorem quotient (B : ℝ) (m : ℕ) :
    radius C B m / C.S.a m = (unit C m)^B :=
  mul_div_cancel_left₀ _ (C.S.a_pos m).ne'

private theorem ordinary : Height C.S atTop C.S.scale id 1 := by
  refine ⟨tendsto_id,tendsto_const_nhds.congr' ?_⟩
  filter_upwards [C.S.divergent.eventually_gt_atTop 0] with m hm
  exact (div_self hm.ne').symm

theorem unit_rate : RateIs atTop C.S.scale (unit C) 0 := by
  have hT := C.S.divergent
  have b := (OPE.Log.betaStamp (C:=C) hT (ordinary C)).zeroCost hT
  refine RateIs.of_sandwich (RateIs.const (c:=1) hT one_pos)
    ((RateLE.const 2 hT).add (b.pays hT) hT) ?_ ?_ hT
  · refine Eventually.of_forall fun m => ?_
    have hh := Real.log_nonneg (C.path.levels.fits.delayed m).le
    dsimp only [unit]
    linarith
  · refine Eventually.of_forall fun m => ?_
    change 2 + Real.log (C.path.levels.clock.hatBeta m) ≤ 2 + C.path.levels.clock.hatBeta m
    linarith [Real.log_le_self (show 0 ≤ C.path.levels.clock.hatBeta m by
      linarith [C.path.levels.fits.delayed m])]

theorem radius_rate (B : ℝ) : RateIs atTop C.S.scale (radius C B) (-1) := by
  change RateIs atTop C.S.scale (fun m => C.S.a m * (unit C m)^B) (-1)
  simpa only [mul_zero, add_zero, id_eq] using
    (ordinary C).mesh.mul ((unit_rate C).rpow B)

theorem fine (B : ℝ) : Tendsto (radius C B) atTop trail :=
  tendsto_nhdsWithin_iff.mpr
    ⟨(radius_rate C B).tends (by norm_num) C.S.divergent,(radius_rate C B).pos⟩

/-- This very lattice index has height one on its own physical clock. -/
theorem stage (B : ℝ) : Height C.S atTop (LogV ∘ radius C B) id 1 := by
  have hh : Tendsto (fun m => -Real.log (radius C B m) / C.S.scale m) atTop (𝓝 1) := by
    simpa only [neg_div,neg_neg] using (radius_rate C B).rate.neg
  refine ⟨tendsto_id,?_⟩
  simpa only [id_eq,Function.comp_apply,LogV,Real.log_inv,inv_div,inv_one] using
    hh.inv₀ (by norm_num)

/-- The original reporting index lies strictly between either pair of
genuine heights straddling one. -/
theorem between (B : ℝ) {b j : ℝ → ℕ} {a c : ℝ}
    (lb : Height C.S trail LogV b a) (lj : Height C.S trail LogV j c)
    (ha : a < 1) (hc : 1 < c) :
    ∀ᶠ m in atTop, b (radius C B m) < m ∧ m < j (radius C B m) :=
  let T := PhysMS.to_log_zoom.comp (fine C B)
  ((lb.comp (fine C B)).earlier ha T (stage C B)).and
    ((stage C B).earlier hc T (lj.comp (fine C B)))

end YM.Integration.WilsonReportingLength
