import YM.Integration.WilsonDegreeFourInheritedRange
import YM.RG01.Slack

/-! The original cutoff in cover length pays the full polynomial expense
of the issued source, before either regulator. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonReceivedAxialCurrency
open Filter Lattice Wilson RG OPE.Therm PhysicalNext.Repeat.Legato WilsonLimitConstruction
open Pert.Asymptotics
open scoped Topology
variable {G : Gauge} (R : Run G) (simple : G.Simple) {η : ℝ} {T : Campaign R}
  {W : Campaign.Pillars R T} (funded : FundedOriginalProperties.{u} simple η W)

include funded in
theorem price (n q : ℕ) {ε : ℝ} (ep : 0 < ε) :
    ∀ᶠ i : ℕ in atTop, ∀ N per, i < N → ∀ a : ℝ,
      (R.family.path.rep N per i).p.supportExponent ≤ a → ∀ D : ℝ,0≤D →
      D ≤ 2^n/(regulatorRun R.family N per (i+1))^(2*n) → ∀ Y : ℝ,
      Real.exp (a*WilsonDegreeFourInheritedRange.height R (q+2*n) i)*Y ≤ 2*D →
      Y ≤ ε*(regulatorRun R.family N per i)^q := by
  let C : ℝ := 2*16^n
  have Cp : 0 < C := by dsimp [C];positivity
  filter_upwards [RG01.Physical.nextHat simple R.family.path.levels,
    WilsonDegreeFourInheritedRange.fee R simple funded (q+2*n) (div_pos ep Cp)] with i step fee
  intro N per cut a ha D Dp hD Y paid
  let β := (R.family.path.rep N per i).beta
  let β' := (R.family.path.rep N per (i+1)).beta
  let g := regulatorRun R.family N per i
  let b := WilsonDegreeFourInheritedRange.height R (q+2*n) i
  let d := (R.family.path.rep N per i).p.supportExponent
  have bp : 0 < β := Overlay.beta_positive R.makes.wilson cut.le
  have fp : 0 < β' := Overlay.beta_positive R.makes.wilson cut
  have band : R.family.path.levels.clock.hatBeta i / 2 ≤ β :=
    (R.makes.wilson.represents N per i cut.le).band.1
  have step' : β' ≤ 2*R.family.path.levels.clock.hatBeta (i+1) :=
    (R.makes.wilson.represents N per (i+1) cut).band.2
  have ratio : β' ≤ 8*β := by linarith only [band,step',step]
  have limit : D ≤ 16^n*β^n := calc
    _ ≤ 2^n/((Real.sqrt β')⁻¹)^(2*n) := hD
    _ = 2^n*β'^n := by rw [div_eq_mul_inv,inv_pow,inv_inv,pow_mul,Real.sq_sqrt fp.le]
    _ ≤ 2^n*(8*β)^n := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ fp.le ratio _) (by positivity)
    _ = _ := by rw [mul_pow,←mul_assoc,←mul_pow];norm_num
  have flat : Real.exp (-(a*b)) ≤ (ε/C)*g^(q+2*n) := calc
    _ ≤ Real.exp (-d*b) := by
      apply Real.exp_le_exp.mpr
      rw [neg_mul]
      exact neg_le_neg (mul_le_mul_of_nonneg_right ha (Nat.cast_nonneg _))
    _ ≤ Real.exp (-d*b)*(R.family.path.levels.params i).columns :=
      le_mul_of_one_le_right (Real.exp_nonneg _) (R.family.path.levels.params i).columns_ge
    _ ≤ _ := fee N per cut.le
  have square : g^2 = β⁻¹ := by
    change ((Real.sqrt β)⁻¹)^2 = β⁻¹
    rw [inv_pow,Real.sq_sqrt bp.le]
  calc
    Y ≤ (2*D)/Real.exp (a*b) := (le_div_iff₀ (Real.exp_pos _)).mpr (by simpa only [mul_comm Y] using paid)
    _ = (2*D)*Real.exp (-(a*b)) := by rw [div_eq_mul_inv,Real.exp_neg]
    _ ≤ (2*(16^n*β^n))*((ε/C)*g^(q+2*n)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left limit (by norm_num)) flat (Real.exp_nonneg _)
        (by positivity)
    _ = ε*g^q := by
      rw [pow_add,pow_mul,square,inv_pow]
      dsimp [C]
      field_simp [bp.ne']
end YM.Integration.WilsonReceivedAxialCurrency
