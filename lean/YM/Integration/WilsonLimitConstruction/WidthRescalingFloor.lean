import YM.FullVolume.Cross
import YM.Integration.FullQLocalStrongApplication

/-! A finite pre-block floor for the external-to-output width inequality. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.WidthRescalingFloor

open Lattice RG RG.Supply FullQLocal PhysicalNext PhysicalNext.Repeat.Legato

/-- The higher profile stage covers all of its possible lower neighbours.
There is no choice of a calendar or block length in this request. -/
def floor (W : ProfileWidths) (transport : ℕ → ℝ) (j : ℕ) : ℕ :=
  (Finset.range (j + 1)).sup fun i =>
    Nat.ceil (2 * transport j / min (min (W.width j) (W.width i)) 1)

theorem pays (W : ProfileWidths) (transport : ℕ → ℝ) (i j : ℕ) (hij : i ≤ j) :
    2 * transport j ≤
      (floor W transport j : ℝ) * min (min (W.width j) (W.width i)) 1 := by
  let u := min (min (W.width j) (W.width i)) 1
  have hu : 0 < u :=
    lt_min (lt_min (W.positive j) (W.positive i)) zero_lt_one
  have hnat : Nat.ceil (2 * transport j / u) ≤ floor W transport j :=
    Finset.le_sup (f := fun k =>
      Nat.ceil (2 * transport j / min (min (W.width j) (W.width k)) 1))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hij))
  exact (div_le_iff₀ hu).mp ((Nat.le_ceil _).trans (by exact_mod_cast hnat))

/-- On any original Run whose raised sheet covers this floor at the upper
profile index, every output width bounded by one satisfies the rescaling
inequality. The block on the right is the literal physical block. -/
theorem on_run {G : Gauge} (R : Run G) (s : Sheet G) (n : ℕ → ℕ)
    (hsheet : R.metals.p = ThroughLaunch.raise s n)
    (W : ProfileWidths) (transport : ℕ → ℝ)
    (positive : ∀ i, 0 ≤ transport i) (m : ℕ)
    (hfloor : floor W transport (R.family.path.levels.clock.J (m + 1)) ≤
      n (R.family.path.levels.clock.J (m + 1)))
    (target : ℝ) (htarget : target ≤ 1) :
    2 * transport (R.family.path.levels.clock.J (m + 1)) * target ≤
      (R.family.path.levels.S.block m).val * min (W.pair R.family m) 1 := by
  let L := R.family.path.levels
  let j := L.clock.J (m + 1)
  have hlen : L.clock.factor = R.rolls.L := R.alloy.B.valid.lengths
  have heq : R.metals.p.floorL j = n j := by rw [hsheet]
  have hn : n j ≤ (R.rolls.L j).val := by
    simpa only [heq] using (R.rolls.large j).need
  have hb : n j ≤ (L.S.block m).val := by
    calc
      _ ≤ (R.rolls.L j).val := hn
      _ = (L.clock.factor j).val := by rw [hlen]
      _ = (L.S.block m).val := by change (L.clock.factor (L.clock.J (m + 1))).val = _; rw [L.fits.sameFactor]
  have hblock : (floor W transport j : ℝ) ≤ (L.S.block m).val := by
    exact_mod_cast hfloor.trans hb
  calc
    _ ≤ 2 * transport j := mul_le_of_le_one_right (mul_nonneg (by norm_num) (positive j)) htarget
    _ ≤ (floor W transport j : ℝ) * min (W.pair R.family m) 1 :=
      pays W transport (L.clock.J m) j (L.fits.mono (Nat.le_succ m))
    _ ≤ _ := mul_le_mul_of_nonneg_right hblock
      (le_min (W.pair_positive R.family m).le zero_le_one)

end YM.Integration.WilsonLimitConstruction.WidthRescalingFloor
end
