import YM.Integration.WilsonOlderFreshSoftSocketVane
import YM.Integration.WilsonOlderFreshSoftSocketFigurePower

/-! The grid of the booked radius and its actual Wilson coupling give simultaneous engineering and monitor bounds. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftSocketStationScale
open Function Filter Finset RG Lattice Wilson Source Labels Next.Rank Next.Rank.Price Next.Rank.Atlas
open Next.Rank.Station Further.CorrectedLift Cells Extraction Table Climb Trace Trace.Pilot Next.UVStress MergeProof.East
open PhysicalNext.Repeat.Legato WilsonPositionThermometerCapStation Pert.Asymptotics
open scoped Classical BigOperators Topology

variable {G:Gauge}(R:Run G)
local notation "road" => R.family.path.levels
local notation "β" => R.family.path.levels.clock.hatBeta

theorem extent (simple:G.Simple){η:ℝ}(pos:0<η):∀ᶠj:ℕ in atTop,∀b:ℝ,b≤Perch.y (β j)→
    Station.mag road b j≤(β j)^η:=by
  have ht:=Real.tendsto_log_atTop.comp (Station.hat_rate road simple)
  filter_upwards [ht.eventually_ge_atTop (2:ℝ),(Real.tendsto_log_atTop.comp ht).eventually_ge_atTop (1:ℝ),
    ht.eventually ((Real.isLittleO_pow_log_id_atTop (n:=3)).bound pos)] with j large later bound
  intro b cap
  let l:=Real.log (β j)
  let z:=Real.log l
  change 2≤l at large
  change 1≤z at later
  change ‖z^3‖≤η*‖l‖ at bound
  have a0:0≤z:=by linarith only [later]
  have l0:0≤l:=by linarith only [large]
  have H0:0<β j:=zero_lt_one.trans ((road).fits.delayed j)
  simp only [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg a0 _),abs_of_nonneg l0] at bound
  calc
    _≤((road).clock.monitor j)^(Perch.y (β j)):=
      Real.rpow_le_rpow_of_exponent_le (Real.one_le_exp (sq_nonneg _)) cap
    _=Real.exp (z^3):=by change (Real.exp (z^2))^z=_;rw [←Real.exp_mul];congr 1
    _≤Real.exp (η*l):=Real.exp_le_exp.mpr bound
    _=(β j)^η:=by rw [Real.rpow_def_of_pos H0];unfold l;rw [mul_comm]

theorem heated (N per K:ℕ)(live:K≤N)(warm:8≤β K)(η:ℝ)(hη:0≤η):
    (β K)^η≤Real.exp ((3*η)*Real.log (regulatorRun R.family N per K)⁻¹):=by
  let hot:=R.family.path.β N per K
  have band:=(R.makes.wilson.represents N per K live).band.1
  change (β K)/2≤hot at band
  have four:(4:ℝ)≤hot:=by linarith only [warm,band]
  have hot0:0≤hot:=by linarith only [four]
  have root0:0<Real.sqrt hot:=Real.sqrt_pos.mpr (by linarith only [four])
  have root:2≤Real.sqrt hot:=by apply (Real.le_sqrt (by norm_num) hot0).mpr;norm_num;exact four
  have buy:β K≤(Real.sqrt hot)^3:=by
    calc
      β K≤2*hot:=by linarith only [band]
      _≤Real.sqrt hot*hot:=mul_le_mul_of_nonneg_right root hot0
      _=Real.sqrt hot*(Real.sqrt hot)^2:=by rw [Real.sq_sqrt hot0]
      _=_:=by ring
  have heat:Real.sqrt hot=(regulatorRun R.family N per K)⁻¹:=by change _=((Real.sqrt hot)⁻¹)⁻¹;rw [inv_inv]
  calc
    _≤((Real.sqrt hot)^3)^η:=Real.rpow_le_rpow (by linarith only [warm]) buy hη
    _=_:=by rw [Real.rpow_def_of_pos (pow_pos root0 _),Real.log_pow,←heat];congr 1;push_cast;ring

end YM.Integration.WilsonOlderFreshSoftSocketStationScale
end
