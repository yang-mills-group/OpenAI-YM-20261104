import YM.Integration.WilsonPhysicalKernelClock
import YM.Integration.WilsonLimitConstruction.FundedWilsonSparsePrice

/-! A positive varying penalty for the complete original finite Wilson flow. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMovingKernelProfile

open Lattice RG Pert.Asymptotics PhysicalNext.Repeat.Legato WilsonLimitConstruction
variable {G : Gauge}

/-- The same additional bare inverse temperature is applied to every
surviving native penalty. Its measured endpoint is the original full profile. -/
def value (R : Run G) (N p : ℕ) (t : ℝ) (i : ℕ) : ℝ :=
  if t=0 then R.family.path.β N p i
  else R.family.path.β N p i+((t^2)⁻¹-R.family.beta N p)

theorem at_top (R : Run G) (N p : ℕ) {t : ℝ} (ht : t ≠ 0) :
    value R N p t N = (t^2)⁻¹ := by
  rw [value,if_neg ht]
  change R.family.beta N p+((t^2)⁻¹-R.family.beta N p) = _
  ring

theorem endpoint (R : Run G) (N p : ℕ) :
    value R N p (regulatorRun R.family N p N) = R.family.path.β N p := by
  funext i
  have ht : 0 < regulatorRun R.family N p N := IterationFour.Currency.g_pos R.makes N p N le_rfl
  have hβ := WilsonPhysicalKernelClock.temperature R N p N le_rfl
  rw [value,if_neg ht.ne',hβ]
  change _+(R.family.beta N p-R.family.beta N p)=_
  rw [sub_self,add_zero]

theorem positive (R : Run G) (N p i : ℕ) (hi : i ≤ N) {t : ℝ} (ht : |t| ≤ regulatorRun R.family N p N) :
    0 < value R N p t i := by
  let g := regulatorRun R.family N p i
  let gN := regulatorRun R.family N p N
  have hg : 0 < g := IterationFour.Currency.g_pos R.makes N p i hi
  have hbase : 0 < R.family.path.β N p i := by
    rw [← WilsonPhysicalKernelClock.temperature R N p i hi]
    exact inv_pos.mpr (sq_pos_of_pos hg)
  by_cases h₀ : t=0
  · simpa only [value,h₀,if_true] using hbase
  have H : t^2 ≤ gN^2 := by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) ht 2
  have htop : (gN^2)⁻¹=R.family.beta N p := WilsonPhysicalKernelClock.temperature R N p N le_rfl
  have hlow : R.family.beta N p ≤ (t^2)⁻¹ := by
    rw [← htop]
    exact inv_anti₀ (sq_pos_of_ne_zero h₀) H
  rw [value,if_neg h₀]
  exact add_pos_of_pos_of_nonneg hbase (sub_nonneg.mpr hlow)

/-- The scale loss of an arbitrary physical block is uniform before the
cutoff, the period, the intermediate level, and the varying coupling. -/
theorem price (R : Run G) (hG : G.Simple) (N p i : ℕ) (hi : i ≤ N) {t : ℝ}
    (ht : |t| ≤ regulatorRun R.family N p N) : |value R N p t i| * t^2 ≤ 17 := by
  let g := regulatorRun R.family N p i
  have hg : 0 < g := IterationFour.Currency.g_pos R.makes N p i hi
  have hβ : (g^2)⁻¹=R.family.path.β N p i := WilsonPhysicalKernelClock.temperature R N p i hi
  have hbasic := ht.trans (FundedWilsonSparsePrice.compare R hG N p i hi)
  have hscale : t^2 ≤ 16*g^2 := by
    have h := pow_le_pow_left₀ (abs_nonneg t) hbasic 2
    rw [sq_abs t,mul_pow] at h
    norm_num at h
    exact h
  have hb : 0 ≤ R.family.path.β N p i := hβ ▸ inv_nonneg.mpr (sq_nonneg g)
  have htop : 0 ≤ R.family.beta N p := by
    have H := WilsonPhysicalKernelClock.temperature R N p N le_rfl
    change 0 ≤ R.family.path.β N p N
    rw [← H]
    positivity
  have hraw : R.family.path.β N p i*t^2 ≤ 16 := by
    calc _ ≤ R.family.path.β N p i*(16*g^2) := mul_le_mul_of_nonneg_left hscale hb
      _ = 16*((g^2)⁻¹*g^2) := by rw [← hβ]; ring
      _ = 16 := by rw [inv_mul_cancel₀ (pow_ne_zero _ hg.ne'),mul_one]
  by_cases h₀ : t=0
  · simp [h₀]
  rw [abs_of_pos (positive R N p i hi ht),value,if_neg h₀,add_mul,sub_mul,
    inv_mul_cancel₀ (pow_ne_zero _ h₀)]
  linarith only [hraw,mul_nonneg htop (sq_nonneg t)]

end YM.Integration.WilsonMovingKernelProfile
