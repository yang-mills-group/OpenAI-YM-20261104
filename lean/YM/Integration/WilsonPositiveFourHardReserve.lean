import YM.Integration.WilsonOriginalCompanionCorridorCurrency
import YM.Integration.WilsonThermometerPhysicalCorridorFare
import YM.Integration.WilsonMeasuredOwnerReserve

/-! A raw canonical hard admission pays its full physical corridor before either regulator. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPositiveFourHardReserve
open Filter Lattice Wilson RG Source PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open ActualRunKernelPackets Pressure Push.PriceCompiler ConnectedActivityE6 Pert.Asymptotics
open scoped Topology Classical
variable {G:Gauge}(R:Run G)(simple:G.Simple)
local notation "A" => R.family.path.levels
local notation "H" => (A).clock.hatBeta

include simple in
/-- The actual before-test square-root forced allowance beats a cubic in the
logarithm of the inverse coupling. -/
theorem cube : ∀ᶠ f:ℕ in atTop,LocalComparison.forcedDivisor R.family f≤
    Real.exp (-(Real.log (H f))^3):=by
  have grows:=Real.tendsto_log_atTop.comp (Next.Rank.Station.hat_rate (A) simple)
  filter_upwards [grows.eventually_ge_atTop 2,(Real.tendsto_log_atTop.comp grows).eventually_ge_atTop 20]
    with f hl hz
  let l:=Real.log (H f)
  let z:=Real.log l
  change 2≤l at hl
  have lp:0<l:=by linarith only [hl]
  change 20≤z at hz
  have bigger:l^4≤(Real.exp (z^2))^((1:ℝ)/5):=by
    calc _=Real.exp (4*z):=by change l^4=Real.exp ((↑(4:ℕ):ℝ)*Real.log l);rw [←Real.log_pow,Real.exp_log (pow_pos lp _)]
         _≤Real.exp (z^2*((1:ℝ)/5)):=Real.exp_le_exp.mpr
           (by nlinarith only [mul_nonneg (show 0≤z-20 by linarith only [hz]) (show 0≤z by linarith only [hz])])
         _=_:=Real.exp_mul _ _
  change Real.sqrt (Real.exp (-((Real.exp (z^2))^((1:ℝ)/5))))≤Real.exp (-l^3)
  apply (Real.sqrt_le_iff).2
  refine ⟨(Real.exp_pos _).le,?_⟩
  rw [sq (Real.exp _),←Real.exp_add]
  apply Real.exp_le_exp.mpr
  have base:2≤l:=hl
  nlinarith only [bigger,mul_nonneg (sub_nonneg.mpr base) (pow_nonneg lp.le 3)]

include simple in
/-- The genuine reserve pays the entire original corridor of length O(log β̂),
including its per-date before-field geometry and any fixed restored test powers. -/
theorem original (c k d q:ℕ):∀ᶠ f:ℕ in atTop,∀n:ℕ,
    (n:ℝ)≤(c:ℝ)*RG16.Lambda (A) f+2 → ∀N p:ℕ,f≤N →
      LocalComparison.forcedDivisor R.family f*(H f)^(k*n+d)≤(regulatorRun R.family N p f)^q:=by
  let C:ℝ:=(k:ℝ)*(3*c+2)+d+q+2
  have grows:=Next.Rank.Station.hat_rate (A) simple
  filter_upwards [cube R simple,(Real.tendsto_log_atTop.comp grows).eventually_ge_atTop C,grows.eventually_ge_atTop 2]
    with f reserve large hot n span N p fn
  let x:=H f
  let z:=Real.log x
  have xp:0<x:=by dsimp [x];linarith only [hot]
  change C≤z at large
  change (n:ℝ)≤(c:ℝ)*(2+z)+2 at span
  have coef:0≤(k:ℝ)*(3*c+2):=by positivity
  have one:1≤z:=by
    dsimp only [C] at large
    linarith only [large,coef,Nat.cast_nonneg (α:=ℝ) d,Nat.cast_nonneg (α:=ℝ) q]
  have span':(n:ℝ)≤(3*c+2)*z:=by nlinarith only [span,one,mul_nonneg (Nat.cast_nonneg (α:=ℝ) c) (sub_nonneg.mpr one)]
  have count:((k*n+d+q:ℕ):ℝ)≤z^2:=by
    push_cast
    calc _≤(k:ℝ)*((3*c+2)*z)+(d:ℝ)*z+(q:ℝ)*z:=by
          gcongr
          · simpa only [mul_one] using (mul_le_mul_of_nonneg_left one (Nat.cast_nonneg (α:=ℝ) d))
          · simpa only [mul_one] using (mul_le_mul_of_nonneg_left one (Nat.cast_nonneg (α:=ℝ) q))
         _≤C*z:=by dsimp [C];nlinarith only [one]
         _≤_:=(mul_le_mul_of_nonneg_right large (zero_le_one.trans one)).trans_eq (sq z).symm
  have raw:Real.exp (-z^3)*x^(k*n+d)≤(x^q)⁻¹:=by
    rw [←one_div]
    apply (le_div_iff₀ (pow_pos xp _)).mpr
    calc _=Real.exp (-z^3)*x^(k*n+d+q):=by rw [pow_add];ring
         _=Real.exp (-z^3+((k*n+d+q:ℕ):ℝ)*Real.log x):=by rw [Real.exp_add,←Real.log_pow,Real.exp_log (pow_pos xp _)]
         _≤1:=Real.exp_le_one_iff.mpr (by change -z^3+_ * z≤0;nlinarith only [mul_le_mul_of_nonneg_right count (zero_le_one.trans one)])
  let g:=regulatorRun R.family N p f
  let β:=R.family.path.β N p f
  have cap:= (R.makes.wilson.represents N p f fn).band.2
  change β≤2*x at cap
  have bcap:β≤x^2:=by
    change 2≤x at hot
    nlinarith only [cap,mul_nonneg (show 0≤x-2 by linarith only [hot]) xp.le]
  have gp:=ActualRunKernelPackets.regulator_pos R N p f fn
  have bound:x⁻¹≤g:=(inv_le_inv₀ xp (inv_pos.mp gp)).mpr ((Real.sqrt_le_iff).mpr ⟨xp.le,bcap⟩)
  exact ((mul_le_mul_of_nonneg_right reserve (pow_nonneg xp.le _)).trans raw).trans
    (by simpa only [inv_pow] using pow_le_pow_left₀ (inv_nonneg.mpr xp.le) bound q)

open WilsonOriginalCompanionCorridorCurrency in
include simple in
theorem earned (c l q:ℕ):∀ᶠ f:ℕ in atTop,∀j:ℕ,
    (f-(j+2):ℕ)≤(c:ℝ)*RG16.Lambda (A) f+2 → ∀N p:ℕ,f≤N →
    LocalComparison.forcedDivisor R.family f*WilsonOriginalCompanionTwinCredit.fare R f j l≤
      constant*(regulatorRun R.family N p f)^q:=by
  filter_upwards [original R simple c 36 (5+(4+6*l)*6) q] with f credit j span N p fn
  have kp:0≤LocalComparison.forcedDivisor R.family f:=Real.sqrt_nonneg _
  calc _≤LocalComparison.forcedDivisor R.family f*(constant*(H f)^(36*(f-(j+2))+(5+(4+6*l)*6))):=
            mul_le_mul_of_nonneg_left (bounded R f j l) kp
       _=constant*(LocalComparison.forcedDivisor R.family f*(H f)^(36*(f-(j+2))+(5+(4+6*l)*6))):=by ring
       _≤_:=mul_le_mul_of_nonneg_left (credit _ span N p fn) (by unfold constant;norm_num)

end YM.Integration.WilsonPositiveFourHardReserve
end
