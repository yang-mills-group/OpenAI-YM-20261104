import YM.Integration.WilsonMeasuredRankedFiledPrimary
import YM.Integration.WilsonMeasuredPrimarySubpower

/-! A common fixed-horizon tariff for the two signed regular returns and
the fully funded fixed-rank coefficient on the selected physical period. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredRankedPrimaryBudget
open Function Filter Set Lattice Wilson RG Source Labels Next.Foundations
open ProjectorNext.Equivariance Trace.Physical.Germ Push.Local
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Extra.Histories
open Push.PriceCompiler ThroughLaunch Roof Push.Local Graces Planned.GuardedAtom
open WilsonLimitConstruction WilsonReportLampForecast QuadraticLocal ConnectedActivityE6
open scoped Topology BigOperators Classical

def wrap {G:Gauge} {d:ℕ} (F:Frame G d) (Y:Hol G) : ℝ :=
  WilsonMeasuredRankedGerm.wrapCost F Y*Real.exp 200

theorem bounded_wrap {G:Gauge} {d:ℕ} (F:Frame G d) (Y:Hol G) (P:BudgetPoint) (n:Side)
    (fixed:P.supportExponent≤100) : WilsonMeasuredRankedGerm.wrapCost F Y*wraps P n≤wrap F Y := by
  apply mul_le_mul_of_nonneg_left _ (WilsonMeasuredRankedGerm.wrapCost_nonneg F Y)
  apply Real.exp_le_exp.mpr
  have cut:0≤P.supportExponent*(n.val:ℝ)/(10*(4*(P.B:ℝ)+2)):=by
    exact div_nonneg (mul_nonneg P.exponent_pos.le (Nat.cast_nonneg _)) (by positivity)
  linarith

theorem scalar {G:Gauge} {d:ℕ} {F:Frame G d} {n:Side} (P:BudgetPoint) (Y:Hol G)
    (S:SectionData F) (y:Site n) (w:ℝ) {θ E b net f:ℝ} (radius:0<θ) (ep:0≤E) (active:0≤b)
    (fixed:P.supportExponent≤100)
    (he:WilsonMeasuredPrimaryTariff.allowance P Y S y w≤f)
    (hc:WilsonMeasuredPrimaryTariff.cost P Y S y w≤f)
    (fn:0≤f)
    (receipt:
      let r:=4*E
      let s:=(factor Y S P.supportExponent w*(P.order.factorial:ℝ))*r
      let c:=(P.order.factorial:ℝ)*r+s+θ*P.mass (S.footprint y) (w*(s/θ))
      net≤2*(r+s)/θ+WilsonMeasuredRankedGerm.wrapCost F Y*wraps P n*(b+c/θ)) :
    θ*net≤(1+wrap F Y)*f*E+wrap F Y*(θ*b) := by
  let r:=4*E
  let s:=(factor Y S P.supportExponent w*(P.order.factorial:ℝ))*r
  let c:=(P.order.factorial:ℝ)*r+s+θ*P.mass (S.footprint y) (w*(s/θ))
  let z:=WilsonMeasuredRankedGerm.wrapCost F Y*wraps P n
  have stock:=WilsonMeasuredPrimaryTariff.funds P Y S y w (r:=E) radius
  have cash:=WilsonMeasuredPrimaryTariff.cash P Y S y w (r:=E) radius ep
  change c/θ=WilsonMeasuredPrimaryTariff.allowance P Y S y w*E/θ at stock
  change 2*max (c/θ) (2*(r+s)/θ)=WilsonMeasuredPrimaryTariff.cost P Y S y w*E/θ at cash
  have low:c/θ≤f*E/θ:=by rw [stock];gcongr
  have both:2*(2*(r+s)/θ)≤f*E/θ:=calc
    _ ≤ 2*max (c/θ) (2*(r+s)/θ):=by gcongr;exact le_max_right _ _
    _ ≤ _ :=by rw [cash];gcongr
  have gross:0≤f*E/θ:=div_nonneg (mul_nonneg fn ep) radius.le
  have head:2*(r+s)/θ≤f*E/θ:=by linarith only [both,gross]
  have zn:0≤z:=mul_nonneg (WilsonMeasuredRankedGerm.wrapCost_nonneg F Y) (Real.exp_pos _).le
  have cap:z≤wrap F Y:=bounded_wrap F Y P n fixed
  have step:net≤f*E/θ+wrap F Y*(b+f*E/θ):=calc
    _ ≤ 2*(r+s)/θ+z*(b+c/θ):=receipt
    _ ≤ f*E/θ+z*(b+f*E/θ):=by gcongr
    _ ≤ _:=by gcongr
  calc
    _ ≤ θ*(f*E/θ+wrap F Y*(b+f*E/θ)):=mul_le_mul_of_nonneg_left step radius.le
    _ = _:=by field_simp [radius.ne'];ring

theorem native {G:Gauge} (R:Run G) (simple:G.Simple)
    {i N:ℕ} (live:i+1≤N) (per:ℕ) :
    let β:=(R.family.path.rep N per (i+1)).beta
    let g:=Coat.gStep β
    0<g ∧ R.alloy.B.a.clock.hatBeta i*g^2 ≤ 2 := by
  intro β g
  have band:=(R.makes.wilson.represents N per (i+1) live).band.1
  change R.alloy.B.a.clock.hatBeta (i+1)/2≤β at band
  have xp:0<R.alloy.B.a.clock.hatBeta (i+1):=zero_lt_one.trans (R.alloy.B.a.fits.delayed (i+1))
  have bp:0<β:=by linarith
  have gp:0<g:=inv_pos.mpr (Real.sqrt_pos.mpr bp)
  have mono:R.alloy.B.a.clock.hatBeta i≤R.alloy.B.a.clock.hatBeta (i+1):=by
    exact (Real.log_le_log_iff (zero_lt_one.trans (R.alloy.B.a.fits.delayed i)) xp).mp
      (WilsonAdmissionScale.logarithm_monotone R.alloy.B.a simple (Nat.le_succ i))
  have id:g^2=β⁻¹:=by
    change (Real.sqrt β)⁻¹^2=β⁻¹
    rw [inv_pow,Real.sq_sqrt bp.le]
  refine ⟨gp,?_⟩
  rw [id,←div_eq_mul_inv]
  exact (div_le_iff₀ bp).mpr (by linarith only [mono,band])

end YM.Integration.WilsonMeasuredRankedPrimaryBudget
