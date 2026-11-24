import YM.Integration.OriginalMarkedLocalDifference
import YM.Integration.OriginalMarkedRunAction

/-! Exterior-local difference of the actual funded negative action. Both
measured densities retain the very same forced charges on every configuration. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.OriginalMarkedLocalPurchase

open Function Lattice Lattice.Corona RG RG.Supply Wilson Org Input
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open UVExtension Mast GapsLocal.Renew Push.GridApprox.Attach
open PhysicalNext.Repeat.Daisy.Charity.RG12
open scoped Classical

variable {G : Gauge} {n : Side}

def relative (current kept : Rep G n) (U V : Config G n) : ℝ :=
  (-Real.log (current.eval U)+Real.log (kept.eval U))-(-Real.log (current.eval V)+Real.log (kept.eval V))

def width (L : Levels G) : ℕ := ⌈1/(L.budget 0).supportExponent⌉₊

theorem width_pays (L : Levels G) (m : ℕ) : 1≤(L.budget m).supportExponent*width L := by
  let a := (L.budget 0).supportExponent
  have ha : 0<a := (L.budget 0).exponent_pos
  have paid : 1≤a*(width L:ℝ) := by
    simpa only [width,mul_comm] using (div_le_iff₀ ha).mp (Nat.le_ceil (1/a))
  exact paid.trans (mul_le_mul_of_nonneg_right (L.fits.deepExp (Nat.zero_le m)) (by positivity))

def fee (L : Levels G) (m : ℕ) (S : Support n) (ε : ℝ) : ℝ :=
  2*((S.card:ℝ)*(17:ℝ)^4*(hitConstant (((L.budget m).B+1)*width L)*ε))

theorem fee_nonneg (L : Levels G) (m : ℕ) (S : Support n) {ε : ℝ} (hε : 0≤ε) :
    0≤fee L m S ε := by
  have positive (k : ℕ) : 0≤hitConstant k :=
    mul_nonneg (by positivity) (tsum_nonneg fun i => (polyExp_pos i).le)
  exact mul_nonneg (by norm_num) (mul_nonneg (by positivity) (mul_nonneg (positive _) hε))

theorem claim (L : Levels G) (m : ℕ) (current kept : Rep G n) (omitted : Activities G n)
    {ε : ℝ} (reg : omitted.RegularFamily (L.budget m)) (paid : omitted.EBound (L.budget m) ε)
    (signed : ∀ U, -Real.log (current.eval U)+Real.log (kept.eval U)=omitted.additive (L.budget m) U)
    (S : Support n) (U V : Config G n) (outside : OriginalMarkedLocalDifference.Outside S U V) :
    |relative current kept U V|≤fee L m S ε := by
  unfold relative fee
  rw [signed U,signed V]
  exact OriginalMarkedLocalDifference.variation omitted (L.budget m) reg paid (width L) (width_pays L m) S U V outside

/-- Exactly the same relative price on any previously funded physical Run,
at its own next-stage regulator and upper cutoff. -/
theorem run (R : Run G) {N per m d : ℕ} (hm : m<N) (A : OriginalMarkedRunAction.Comparison R (p:=per) hm d)
    (S : Support (R.family.side m per)) (U V : Config G (R.family.side m per))
    (outside : OriginalMarkedLocalDifference.Outside S U V) :
    |relative (R.family.path.rep N per m) (OriginalMarkedRunAction.approximation R (p:=per) hm d) U V| ≤
      fee R.alloy.B.a m S ((Real.sqrt 2*Pert.Asymptotics.regulatorRun R.family N per (m+1))^(d+1)) :=
  claim R.alloy.B.a m (R.family.path.rep N per m) (OriginalMarkedRunAction.approximation R (p:=per) hm d)
    (OriginalMarkedRunAction.remainder R (p:=per) hm d) A.posterior.cut.regular A.posterior.cut.boundE A.signed S U V outside

end YM.Integration.OriginalMarkedLocalPurchase
