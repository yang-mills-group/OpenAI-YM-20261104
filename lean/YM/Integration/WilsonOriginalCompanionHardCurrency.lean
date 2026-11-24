import YM.Integration.WilsonThermometerPhysicalCorridorFare
import YM.Integration.WilsonMeasuredOwnerReserve

/-! A raw canonical hard admission pays its full physical corridor before either regulator. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCompanionHardCurrency
open Filter Lattice Wilson RG Source PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open ActualRunKernelPackets Pressure Push.PriceCompiler ConnectedActivityE6 Pert.Asymptotics
open scoped Topology Classical
variable {G:Gauge}(R:Run G)(simple:G.Simple)
local notation "A" => R.family.path.levels
local notation "H" => (A).clock.hatBeta

include simple in
theorem reserve : ∀ᶠ f:ℕ in atTop,LocalComparison.forcedDivisor R.family f≤
    Real.exp (-((((A).budget f).B/8:ℕ):ℝ)):=by
  have grows:=Real.tendsto_log_atTop.comp (Next.Rank.Station.hat_rate (A) simple)
  filter_upwards [grows.eventually_ge_atTop 1,(Real.tendsto_log_atTop.comp grows).eventually_ge_atTop 10]
    with f hl hz
  let l:=Real.log (H f)
  let z:=Real.log l
  have lp:0<l:=zero_lt_one.trans_le hl
  change 10≤z at hz
  let b:=((A).budget f).B
  have bc:(b:ℝ)≤l^2+1:=(Nat.ceil_lt_add_one (sq_nonneg l)).le
  have bd:(((b/8:ℕ):ℝ))*8≤(b:ℝ):=by exact_mod_cast Nat.div_mul_le_self b 8
  have grow:l^2≤(Real.exp (z^2))^((1:ℝ)/5):=by
    calc
      _ = Real.exp (2*z):=by rw [two_mul,Real.exp_add,Real.exp_log lp]; ring
      _ ≤ Real.exp (z^2*((1:ℝ)/5)):=Real.exp_le_exp.mpr (by nlinarith [mul_nonneg (by linarith :0≤z-10) (by linarith :0≤z)])
      _ = _:=Real.exp_mul _ _
  change Real.sqrt (Real.exp (-((Real.exp (z^2))^((1:ℝ)/5)))) ≤ Real.exp (-((b/8:ℕ):ℝ))
  apply (Real.sqrt_le_iff).2
  refine ⟨(Real.exp_pos _).le,?_⟩
  rw [sq (Real.exp _),←Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith only [show 1≤l^2 from one_le_pow₀ hl,bd,bc,grow]

include simple in
theorem original (c k d q:ℕ):∀ᶠ f:ℕ in atTop, ∀n:ℕ,
    (n:ℝ)≤(c:ℝ)*Real.log (RG16.Lambda (A) f)+2 → ∀N per:ℕ,f≤N →
    LocalComparison.forcedDivisor R.family f*(H f)^(k*n+d)≤(regulatorRun R.family N per f)^q:=by
  filter_upwards [reserve R simple,WilsonThermometerPhysicalCorridorFare.original R simple c k d q]
    with f raw bill n span N per top
  exact (mul_le_mul_of_nonneg_right raw (pow_nonneg (((A).fits.delayed f).le.trans' (by norm_num)) _)).trans
    (bill n span N per top)

end YM.Integration.WilsonOriginalCompanionHardCurrency
end
