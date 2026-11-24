import YM.Integration.WilsonDegreeFourInheritedTail
import YM.Integration.WilsonLimitConstruction.FundedOriginalRun

/-! A cutoff in the original registered regular rows chosen before the
period, ultraviolet regulator, held exterior, and two submitted labels. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonDegreeFourInheritedRange
open Filter Function MeasureTheory Lattice RG Wilson Source Push.Local
open PhysicalNext.Repeat.Legato WilsonLimitConstruction Pert.Asymptotics WilsonInheritedRegisteredField
open scoped Classical
variable {G : Gauge} (R : Run G) (simple : G.Simple) {η : ℝ} {T : Campaign R}
  {W : Campaign.Pillars R T} (funded : FundedOriginalProperties.{u} simple η W)
local notation "β" => R.family.path.levels.clock.hatBeta

def height (q k : ℕ) : ℕ := ⌈((q+2:ℕ):ℝ)*Real.log (β k)⌉₊

include simple funded in
theorem fee (q : ℕ) {ε : ℝ} (he : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ N per, k ≤ N →
    Real.exp (-(R.family.path.rep N per k).p.supportExponent*(height R q k:ℝ)) *
      (R.family.path.levels.params k).columns ≤ ε*(regulatorRun R.family N per k)^q := by
  let S := R.family.path.levels
  have rise : Tendsto (β) atTop atTop := tendsto_atTop_add_const_left _ _
    (S.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos simple))
  filter_upwards [rise.eventually (eventually_ge_atTop (2:ℝ)),
    rise.eventually (eventually_ge_atTop ε⁻¹)] with k two tiny
  intro N per hk
  let a := β k
  let b := R.family.path.β N per k
  have ap : 0 < a := zero_lt_two.trans_le two
  have bp : 0 < b := Overlay.beta_positive R.makes.wilson hk
  have g : a⁻¹ ≤ regulatorRun R.family N per k := by
    have band : b ≤ 2*a := (R.makes.wilson.represents N per k hk).band.2
    have squared : b ≤ a^2 := by nlinarith only [band,mul_nonneg (sub_nonneg.mpr two) ap.le]
    change a⁻¹ ≤ (Real.sqrt b)⁻¹
    apply inv_anti₀ (Real.sqrt_pos.mpr bp)
    exact (Real.sqrt_le_sqrt squared).trans_eq (Real.sqrt_sq ap.le)
  have small : a⁻¹ ≤ ε := by
    calc
      _ ≤ (ε⁻¹)⁻¹ := inv_anti₀ (inv_pos.mpr he) tiny
      _ = ε := inv_inv _
  have cols : (S.params k).columns ≤ a := funded.2.1.logBudget.money.present k
  have exponent : (R.family.path.rep N per k).p.supportExponent = 100 := by
    have state : (R.family.path.rep N per k).p=R.family.path.levels.budget k :=
      (R.makes.wilson.represents N per k hk).vac
    rw [state]
    exact funded.2.1.paid.fixed k
  have room : ((q+2:ℕ):ℝ)*Real.log a ≤ (height R q k:ℝ) := Nat.le_ceil _
  have loss : Real.exp (-(R.family.path.rep N per k).p.supportExponent*(height R q k:ℝ)) ≤
      a⁻¹^(q+2) := by
    rw [exponent]
    calc
      _ ≤ Real.exp (-(((q+2:ℕ):ℝ)*Real.log a)) := Real.exp_le_exp.mpr (by
        have scale : (height R q k:ℝ) ≤ 100*(height R q k:ℝ) :=
          le_mul_of_one_le_left (Nat.cast_nonneg _) (by norm_num)
        simpa only [neg_mul] using neg_le_neg (room.trans scale))
      _ = _ := by rw [Real.exp_neg,Real.exp_nat_mul,Real.exp_log ap,inv_pow]
  calc
    _ ≤ a⁻¹^(q+2)*a := mul_le_mul loss cols (zero_le_one.trans (S.params k).columns_ge) (by positivity)
    _ = a⁻¹*a⁻¹^q := by rw [pow_succ,pow_succ]; field_simp
    _ ≤ _ := mul_le_mul small (pow_le_pow_left₀ (inv_nonneg.mpr ap.le) g q)
      (pow_nonneg (inv_nonneg.mpr ap.le) _) he.le

include simple funded in
theorem original (q : ℕ) {ε : ℝ} (he : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ N per (hk : k≤N) d, R.family.ref d≤k →
    ∀ (w : R.family.label d) (o : Site (R.family.side k per)) (U : Config G (R.family.side k per)),
    let Z := packet R.makes hk w o
    ‖WilsonDegreeFourInheritedTail.tail R.makes hk w o (height R q k) U‖ ≤
      ε*(regulatorRun R.family N per k)^q*(R.family.labels.level d).coeffSize
        ((R.family.labels.level d).core Z.x) := by
  filter_upwards [fee R simple funded q he] with k price
  intro N per hk d ref w o U Z
  have use := WilsonDegreeFourInheritedTail.field R.makes hk ref w o (height R q k) U
  dsimp only at use
  rw [←mul_assoc] at use
  exact use.trans (mul_le_mul_of_nonneg_right (price N per hk)
    (Finset.sum_nonneg fun _ _=>norm_nonneg _))

end YM.Integration.WilsonDegreeFourInheritedRange
end
