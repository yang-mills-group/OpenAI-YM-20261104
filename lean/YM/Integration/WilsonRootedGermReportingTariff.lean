import YM.Integration.WilsonRootedGermDenseIncome

/-! Spend the filed covariate's polynomial price against the physical running coupling. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedGermReportingTariff
open Function Filter RG PhysicalNext.Repeat.Legato Trace.Terrace Pert.Asymptotics
open scoped Classical Topology
variable {G : Gauge} (R : Run G)

theorem earned (hG : G.Simple) (s q : ℕ) {C ε : ℝ} (hε : 0<ε) :
    ∀ᶠ i : ℕ in atTop, ∀ N p, i≤N →
      C*(R.family.path.levels.clock.hatBeta i)^s * Real.exp (-((s+q+1:ℕ):ℝ)*Lyra R.family.path.levels i) ≤
        ε * regulatorRun R.family N p i^q := by
  let L := R.family.path.levels
  have growth := Next.Rank.Station.hat_rate L hG
  filter_upwards [growth.eventually_ge_atTop 2,growth.eventually_ge_atTop (C/ε)] with i two cash
  intro N p live
  let t := L.clock.hatBeta i
  let g := regulatorRun R.family N p i
  let β := R.family.path.β N p i
  change 2≤t at two
  change C/ε≤t at cash
  have ht : 0<t := zero_lt_two.trans_le two
  have bp : 0<β := Overlay.beta_positive R.makes.wilson live
  have band : β≤2*t := (R.makes.wilson.represents N p i live).band.2
  have quadratic : β≤t^2 := band.trans (by nlinarith only [mul_nonneg ht.le (sub_nonneg.mpr two)])
  have root : Real.sqrt β≤t := Real.sqrt_le_iff.mpr ⟨ht.le,quadratic⟩
  have fg : t⁻¹≤g := inv_anti₀ (Real.sqrt_pos.mpr bp) root
  have paid : C/t≤ε := (div_le_iff₀ ht).mpr ((div_le_iff₀ hε).mp cash |>.trans_eq (mul_comm t ε))
  change C*t^s*Real.exp (-((s+q+1:ℕ):ℝ)*Real.log t)≤ε*g^q
  calc
    _ = (C/t)*(t⁻¹)^q := by
      rw [neg_mul,Real.exp_neg,Real.exp_nat_mul,Real.exp_log ht,pow_succ,pow_add,inv_pow]
      field_simp [ht.ne']
    _ ≤ _ := mul_le_mul paid (pow_le_pow_left₀ (inv_nonneg.mpr ht.le) fg q) (pow_nonneg (inv_nonneg.mpr ht.le) _) hε.le

end YM.Integration.WilsonRootedGermReportingTariff
