import YM.Integration.OriginalCensusFusion
import YM.RG01.Slack

/-! The original forced allowance is flat at the actual coarse coupling,
uniformly across every later cutoff and torus period. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.OriginalForcedFlat

open Filter Lattice Wilson WilsonStartup RG RG.Shoot Marker
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open IterationFour IterationFour.Vacuum Pert.Asymptotics
open scoped Topology

variable {G : Gauge}

/-- Use the beta band of the recorded physical representative at the
requested coarse scale, including the ultraviolet endpoint. -/
theorem allowance (R : Run G) (hG : G.Simple) (r : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, ∀ N per : ℕ, m ≤ N →
      R.family.path.levels.clock.forcedAllowance m ≤ ε*regulatorRun R.family N per m^r := by
  let A := R.family.path.levels
  have htwo : 0 < (2:ℝ)^r := pow_pos (by norm_num) _
  have hsmall := (RG01.Physical.shrink hG A r).eventually_lt_const (div_pos hε htwo)
  filter_upwards [hsmall] with m hm N per hN
  let β := (R.family.path.rep N per m).beta
  have hrecord : R.family.path.Conv N per m := R.makes.wilson.represents N per m hN
  have hh : 1 < A.clock.hatBeta m := A.fits.delayed m
  have hband : β ∈ Set.Icc (A.clock.hatBeta m / 2) (2*A.clock.hatBeta m) := hrecord.band
  have hβ : 0 < β := (div_pos (zero_lt_one.trans hh) (by norm_num)).trans_le hband.1
  have hs : Real.sqrt β ≤ 2*A.clock.hatBeta m := by
    nlinarith [Real.sq_sqrt hβ.le,sq_nonneg (Real.sqrt β-1),hband.2]
  change A.clock.forcedAllowance m ≤ ε*((Real.sqrt β)⁻¹)^r
  rw [inv_pow,← div_eq_mul_inv, le_div_iff₀ (pow_pos (Real.sqrt_pos.2 hβ) _)]
  calc
    _ ≤ A.clock.forcedAllowance m*(2*A.clock.hatBeta m)^r :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.sqrt_nonneg _) hs _) (Real.exp_nonneg _)
    _ = 2^r*(A.clock.hatBeta m^r*A.clock.forcedAllowance m) := by rw [mul_pow];ring
    _ ≤ 2^r*(ε/2^r) := mul_le_mul_of_nonneg_left hm.le htwo.le
    _ = _ := mul_div_cancel₀ _ htwo.ne'

/-- Reuse the same forced addresses, functions, and pointwise majorants. -/
theorem weaken {n : Side} (A : Activities G n) (p : BudgetPoint) {u v : ℝ}
    (h : A.KBound p u) (hprice : u ≤ v) : A.KBound p v := by
  obtain ⟨b,hb,hcost⟩ := h
  exact ⟨b,hb,fun x => ⟨(hcost x).1,(hcost x).2.1,(hcost x).2.2.trans hprice⟩⟩

end YM.Integration.OriginalForcedFlat
end
