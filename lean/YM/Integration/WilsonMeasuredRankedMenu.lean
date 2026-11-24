import YM.Integration.WilsonMeasuredRankedPrimaryBudget

/-! Select one original column and derivative allowance before all positions,
ultraviolet cutoffs, periods and perturbative orders. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredRankedMenu
open Function Filter Set Lattice Wilson RG Source Labels Next.Foundations
open ProjectorNext.Equivariance Trace.Physical.Germ Push.Local
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Extra.Histories
open Push.PriceCompiler ThroughLaunch Roof Push.Local Graces Planned.GuardedAtom
open WilsonLimitConstruction WilsonReportLampForecast
open scoped Topology BigOperators Classical
universe u
variable {G:Gauge} (R:Run G) (d:ℕ)

structure Menu where
  cost:ℝ
  positive:0<cost
  onset:ℕ
  slots : ∀ (i : ℕ) (_ : onset ≤ i) {n : Side} (o : Site n),
    let P:=R.alloy.B.a.budget i
    let w:=Next.Foundations.price G (max P.order P.power)
    WilsonMeasuredPrimaryTariff.allowance P R.family.params (R.family.localSection d) o w≤
      cost*R.alloy.B.a.clock.hatBeta i ∧
    WilsonMeasuredPrimaryTariff.cost P R.family.params (R.family.localSection d) o w≤
      cost*R.alloy.B.a.clock.hatBeta i

theorem original (simple:G.Simple) {T:Campaign R} (W:Campaign.Pillars R T)
    {δ:ℝ} (fund:FundedOriginalProperties.{u} simple δ W) (slow:WilsonWindowReportingPace.Slow R.kit)
    (room:Ready R.family.path.levels) : Nonempty (Menu R d) := by
  obtain ⟨K,kp,offered⟩:=WilsonMeasuredPrimarySubpower.original R simple W fund slow room d
    (show (0:ℝ)<1 by norm_num)
  obtain ⟨onset,enrolled⟩:=eventually_atTop.mp offered
  refine ⟨⟨K,kp,onset,fun i hi n o=>?_⟩⟩
  simpa only [Real.rpow_one] using enrolled i hi o

variable (M:Menu R d)
local notation "ω" => WilsonMeasuredRankedPrimaryBudget.wrap (R.family.labels.level d) R.family.params
local notation "base" => WilsonMeasuredRankedResidual.sourceCost R d

def cost : ℝ := 1+ω+(1+ω)*6*M.cost/(9*base)
def fee (ε:ℝ) : ℝ := ε/cost R d M

theorem cost_positive : 0<cost R d M := by
  have z:0≤ω:=mul_nonneg (WilsonMeasuredRankedGerm.wrapCost_nonneg ..) (Real.exp_pos _).le
  have ones:0≤1+ω:=by linarith
  have st:=M.positive
  have bp:=WilsonMeasuredRankedResidual.sourceCost_pos R d
  dsimp only [cost]; positivity

theorem fee_positive {ε:ℝ} (ep:0<ε) : 0<fee R d M ε:=div_pos ep (cost_positive R d M)

theorem paid (q:ℕ) {ε:ℝ} (ep:0<ε) :
    let r:=fee R d M ε
    let δ:=WilsonMeasuredRankedResidual.tolerance R d q r
    r+((1+ω)*(6*M.cost*(2:ℝ)^q)*δ+ω*r) ≤ ε := by
  intro r δ
  have wr:0≤ω:=mul_nonneg (WilsonMeasuredRankedGerm.wrapCost_nonneg ..) (Real.exp_pos _).le
  have qpos:0<(2:ℝ)^q:=by positivity
  have bs:=WilsonMeasuredRankedResidual.sourceCost_pos R d
  have cap:δ≤r/(9*base*(2:ℝ)^q):=min_le_right _ _
  have p:0≤(1+ω)*(6*M.cost*(2:ℝ)^q):=by have m:=M.positive;positivity
  have top:(1+ω)*(6*M.cost*(2:ℝ)^q)*δ≤(1+ω)*6*M.cost/(9*base)*r := calc
    _ ≤ (1+ω)*(6*M.cost*(2:ℝ)^q)*(r/(9*base*(2:ℝ)^q)):=mul_le_mul_of_nonneg_left cap p
    _ = _:=by field_simp [bs.ne',qpos.ne']
  calc
    _ ≤ (1+ω+(1+ω)*6*M.cost/(9*base))*r:=by linarith only [top]
    _ = ε:=by change cost R d M*(ε/cost R d M)=ε;field_simp [(cost_positive R d M).ne']

end YM.Integration.WilsonMeasuredRankedMenu
