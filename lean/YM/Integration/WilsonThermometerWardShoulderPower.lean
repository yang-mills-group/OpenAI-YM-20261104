import YM.Integration.WilsonThermometerWardShoulderWallet
import YM.Integration.WilsonReceivedCloseChainFunding

/-! A fixed coupling-power restoration for the corrected three-field source
on the finite physical interval and the funded close stage. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerWardShoulderPower
open Filter Finset Lattice Wilson RG Source Labels QuadraticLocal QuadraticLocal.Advent AllOrder PhysMS
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Pert.Asymptotics
open Pressure Push.PriceCompiler AllOrder.Floe.Step WilsonOriginalStarSceneRent WilsonOriginalThermometerPalette
open scoped Topology BigOperators Classical
variable {G:Gauge} (R:Run G)
local notation "hat" => R.alloy.B.a.clock.hatBeta
local notation "budget" => budgetR R
local notation "marks" => Stock.census (Fin 3)
local notation "cash" => max 1 (wallet R levels 0)

private theorem floor {x z K Y σ H:ℝ} (T:ℕ) (xp:0<x) (room:x≤1) (zp:0<z) (adj:x≤3*z)
    (yp:0≤Y) (kp:0≤K) (sp:0≤σ) (hp:0≤H) (paid:K≤(x⁻¹)^(7*T)*Y) (real:H≤4*(z⁻¹)^2):
    ((1+K)*σ*H^3)^3*z⁻¹ ≤ (((1+Y)*σ*36^3)^3*3)*(x⁻¹)^(21*T+19):=by
  let a:=x⁻¹
  have a1:1≤a:=one_le_inv₀ xp |>.mpr room
  have ap:0≤a:=zero_le_one.trans a1
  have inverse:z⁻¹≤3*a:=by
    change z⁻¹≤3*x⁻¹
    rw [←one_div,←div_eq_mul_inv]
    exact (div_le_div_iff₀ zp xp).mpr (by linarith)
  have Hbound:H≤36*a^2:=by
    refine real.trans ((mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (inv_pos.mpr zp).le inverse 2)
      (by norm_num : (0:ℝ)≤4)).trans_eq ?_)
    ring
  have one:1+K≤a^(7*T)*(1+Y):=by
    rw [mul_add,mul_one]
    exact add_le_add (one_le_pow₀ a1) paid
  have top:(1+K)*σ*H^3≤((1+Y)*σ*36^3)*a^(7*T+6):=by
    refine (mul_le_mul (mul_le_mul_of_nonneg_right one sp) (pow_le_pow_left₀ hp Hbound 3)
      (pow_nonneg hp _) (mul_nonneg (mul_nonneg (pow_nonneg ap _) (by linarith)) sp)).trans_eq ?_
    rw [pow_add]
    ring
  have b0:0≤(1+K)*σ*H^3:=mul_nonneg (mul_nonneg (by linarith) sp) (pow_nonneg hp _)
  refine (mul_le_mul (pow_le_pow_left₀ b0 top 3) inverse (inv_pos.mpr zp).le
    (pow_nonneg (b0.trans top) 3)).trans_eq ?_
  rw [mul_pow,←pow_mul]
  change ((((1+Y)*σ*36^3)^3*a^((7*T+6)*3))*(3*a)) = _*a^(21*T+19)
  rw [show 21*T+19=((7*T+6)*3)+1 by omega,pow_succ]
  ring

theorem original (simple:G.Simple) (degree:ℕ) {cap:ℝ} (base:0≤cap):
    ∀ᶠ b:ℕ in atTop,∀m≤b,PaceR.Close R degree cap m b→∀per j,m≤j→j≤b→
    let x:=regulatorRun R.family (b+1) per j
    x≤1→∀(D:PlanV.Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
    (φ:ℕ→ℕ)(_paid:WilsonMovingMentorRootRadius.Income (M:=R.metals) D φ R.alloy.delay)
    (k:ℕ)(_available:k≤R.alloy.B.a.clock.J (b+1))
    (_width:WilsonOriginalThermometerTollBudget.reach R≤R.alloy.B.a.clock.J (b+1)+1)
    (Ω K h Y:ℝ)(T:ℕ),1≤Ω→Ω≤budget b→0≤K→1≤h→h≤∏l∈Ico j b,(budget l)^2*(budget (l+1))^7→
    0≤Y→K≤(x⁻¹)^(7*T)*Y→
    let A:=max 1 ((1+K)*wallet R levels (Poetry.Agenda.seed D φ k (R.alloy.B.a.clock.J (b+1))))*Ω
    ∀(w:Fin 3→ℝ)(c:(marks).Mode→ℂ),WilsonGeometricSignedCapture.weightBill c w=(∑s,‖c s‖*(A*h)^s.val.card)→
    x^(21*T+19)*WilsonGeometricSignedCapture.weightBill c w≤(∑s,‖c s‖)*(((1+Y)*cash*36^3)^3*3):=by
  filter_upwards [WilsonThermometerWardShoulderWallet.original R simple degree base (zero_lt_one:0<(1:ℝ)),
    WilsonReceivedCloseChainFunding.upper R simple degree cap,RG01.Physical.nextHat simple R.alloy.B.a]
    with b fees extent next
  intro m mb close per j mj jb x x1 D φ paid k available width Ω K h Y T op eligible kp hp bill yp earned A w c wedge
  let z:=regulatorRun R.family (b+1) per b
  obtain ⟨xp,adj⟩:=extent m mb close (b+1) per b.le_succ j mj (jb.trans b.le_succ)
  have zp:0<z:=(extent m mb close (b+1) per b.le_succ b mb b.le_succ).1
  let β:=R.family.path.β (b+1) per b
  have original:hat b/2≤β:=(R.makes.wilson.represents (b+1) per b b.le_succ).band.1
  have heat:0<hat b:=zero_lt_one.trans (R.alloy.B.a.fits.delayed b)
  have inverse:(z⁻¹)^2=β:=by
    change (((Real.sqrt β)⁻¹)⁻¹)^2=β
    rw [inv_inv,Real.sq_sqrt (by linarith)]
  have upper:hat (b+1)≤4*(z⁻¹)^2:=by rw [inverse]; linarith only [next,original]
  have row:=fees m mb close per j mj jb D φ paid k available width Ω K h op eligible kp hp bill w c wedge
  rw [Real.rpow_neg_one] at row
  have bound:=floor (σ:=cash) T xp x1 zp adj yp kp (zero_le_one.trans (le_max_left ..))
    (zero_le_one.trans (R.alloy.B.a.fits.delayed (b+1)).le) earned upper
  have summed:0≤∑s,‖c s‖:=Finset.sum_nonneg fun _ _=>norm_nonneg _
  have law:WilsonGeometricSignedCapture.weightBill c w ≤
      (∑s,‖c s‖)*(((1+Y)*cash*36^3)^3*3)*(x⁻¹)^(21*T+19):=by
    apply row.trans
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left bound summed
  calc
    _≤x^(21*T+19)*((∑s,‖c s‖)*(((1+Y)*cash*36^3)^3*3)*(x⁻¹)^(21*T+19)) :=
      mul_le_mul_of_nonneg_left law (pow_nonneg xp.le _)
    _=_:=by
      rw [inv_pow,mul_left_comm, mul_inv_cancel₀ (pow_ne_zero _ xp.ne'),mul_one]

end YM.Integration.WilsonThermometerWardShoulderPower
