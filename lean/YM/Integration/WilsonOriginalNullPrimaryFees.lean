import YM.Integration.WilsonMeasuredRankedMenu
import YM.Integration.WilsonOriginalNullStock
import YM.Integration.WilsonMeasuredNullWrappedDate
import YM.OPE.Height

/-! Fixed physical column cost at the upper and lower dates of an original
step. The supporting footprint retains its original centre. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalNullPrimaryFees
open Filter Labels Lattice Wilson RG Source Trace.Physical Trace.Physical.Germ
open PhysicalNext Repeat Legato Graces Roost Org Push.Local Extra.Histories Next.Foundations
open scoped Classical Topology

variable {G:Gauge} {d:ℕ} {n:Side} {F:Frame G d}

theorem tariff (p : BudgetPoint) (A : Hol G) (S : SectionData F)
    (o : Site n) {w : ℝ} (hw : 0≤w) :
    let b:=WilsonMeasuredPrimaryTariff.allowance p A S o w
    factor A S p.supportExponent w ≤ b ∧ p.mass (S.footprint o) w ≤ b := by
  intro b
  let f : ℝ:=p.order.factorial
  let ζ := factor A S p.supportExponent w
  let z := ζ*f
  have hf : 1≤f := by dsimp [f]; exact_mod_cast (show 1≤p.order.factorial from p.order.factorial_pos)
  have e : 0≤(p.supportExponent+2)*(atomTiles S:ℝ) :=
    mul_nonneg (by linarith only [p.exponent_pos]) (Nat.cast_nonneg _)
  have hζ : 1≤ζ := one_le_mul_of_one_le_of_one_le (Real.one_le_exp e) (atomPrice_ge_one A F hw)
  have hh : ζ≤z := le_mul_of_one_le_right (zero_le_one.trans hζ) hf
  have hmw : p.mass (S.footprint o) w≤p.mass (S.footprint o) (w*z) := by
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    exact le_mul_of_one_le_right hw (hζ.trans hh)
  have nonneg : 0≤p.mass (S.footprint o) w:=mul_nonneg (Real.exp_pos _).le hw
  change ζ≤4*(f+z+p.mass (S.footprint o) (w*z)) ∧
    p.mass (S.footprint o) w≤4*(f+z+p.mass (S.footprint o) (w*z))
  constructor <;> linarith only [hf,hζ,hh,hmw,nonneg]

variable (R:Run G) (d:ℕ)
local notation "section₀" => R.family.localSection d
local notation "budget₀" j:max => R.family.path.levels.budget j
local notation "toll₀" j:max => price G (max (budget₀ j).order (budget₀ j).power)
local notation "staff₀" j:max => factor R.family.params section₀ (budget₀ j).supportExponent (toll₀ j)
local notation "forecast₀" j:max => R.family.path.levels.clock.hatBeta j
local notation "scale₀" j:max => R.family.S.scale j
local notation "block₀" j:max => GermGraph.factor R.family j

/-- Both column currencies are paid before the roots and period are selected. -/
theorem slots (M:WilsonMeasuredRankedMenu.Menu R d) (i : ℕ) (hi : M.onset ≤ i) {n:Side}
    (o : Site n) : staff₀ i ≤ M.cost*forecast₀ i ∧ (budget₀ i).mass ((section₀).footprint o) (toll₀ i) ≤ M.cost*forecast₀ i := by
  have h := (M.slots i hi o).1
  have t := tariff (w:=toll₀ i) (budget₀ i) R.family.params section₀ o (zero_le_one.trans (price_one_le G _))
  exact ⟨t.1.trans h,t.2.trans h⟩

/-- The forecast and the block factor on the physical schedule itself. -/
theorem forecast (i : ℕ) :
    forecast₀ i ≤ (|R.family.path.levels.clock.bar|+|G.slopeConstant|+1)*Real.exp (scale₀ i) ∧
    block₀ i ≤ Real.exp (scale₀ (i+1)) := by
  let S:=R.family.S
  have nonneg (j : ℕ) : 0≤S.scale j := by
    have h := (OPE.scale_mono S).monotone (Nat.zero_le j)
    simpa only [Schedule.scale_zero] using h
  have one := Real.one_le_exp (nonneg i)
  have ss : S.scale i ≤ Real.exp (S.scale i) := by linarith only [Real.add_one_le_exp (S.scale i)]
  constructor
  · change R.family.path.levels.clock.bar + G.slopeConstant*S.scale i ≤ _
    have base := le_mul_of_one_le_right (abs_nonneg R.family.path.levels.clock.bar) one
    have hb := (mul_le_mul_of_nonneg_right (le_abs_self G.slopeConstant) (nonneg i)).trans
      (mul_le_mul_of_nonneg_left ss (abs_nonneg G.slopeConstant))
    have hc := le_abs_self R.family.path.levels.clock.bar
    linarith only [base,hb,hc,one]
  · change ((S.block i).val:ℝ) ≤ Real.exp (S.scale (i+1))
    rw [S.scale_succ,Real.exp_add,Real.exp_log (Nat.cast_pos.mpr (S.block i).pos)]
    exact le_mul_of_one_le_left (Nat.cast_nonneg _) one

end YM.Integration.WilsonOriginalNullPrimaryFees
