import YM.Integration.WilsonMovingMentorTerrace
import YM.Next.SCHEDULE.Dues

/-! The elected course's own measured coupling and its adjacent forecast.
The threshold is removed using the physical clock at the same date. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetTorusScalarClock
open Function Filter Finset Lattice Wilson RG RG.Supply Pressure Input Org Precision Tree
open Next.Scheduling Next.Scheduling.Clock AnalyticBridge VerifiedReset ConnectedActivityE6 PhysicalNext Repeat
open Progress.DirectedRecipe Payments Push AbsoluteSums PriceCompiler
open AllOrder AllOrder.Transit WheelP AllOrder.Floe AllOrder.Floe.Step PlanV Pane ThroughLaunch
open Roost Legato Graces Extra.Iteration Extra.Histories
open QuadraticLocal
open scoped Topology BigOperators Classical
variable {G:Gauge}(R:Run G)
local notation "A" => R.alloy.B.a

def forecast (Γ:ℕ→Pace.Coin)(N per j k:ℕ):ℝ:=
  Wheel.now (Γ j) (Burn.horizon k+2) (R.T.history N per (j+1)).beta

private theorem young {x:ℝ}(hx:1<x)(k d:ℕ)(grade:d≤Burn.horizon k):
    Burn.young x k≤(Clock.gap x)^(d+2):=by
  calc
    Burn.young x k ≤ x^((-(1/2):ℝ)*(d+2)):=by
      rw [Burn.young,Burn.sale_eq]
      apply Real.rpow_le_rpow_of_exponent_le hx.le
      have he:(d:ℝ)≤(Burn.horizon k:ℝ):=by exact_mod_cast grade
      linarith
    _ = _:=by
      rw [Clock.gap,Real.sqrt_eq_rpow,←Real.rpow_neg (zero_le_one.trans hx.le),
        ←Real.rpow_natCast,←Real.rpow_mul (zero_le_one.trans hx.le)]
      push_cast
      ring_nf

theorem threshold {N b j per k:ℕ}{π:ℕ→Layout G}{Γ:ℕ→Pace.Coin}
    {H:(i:ℕ)→RG.Rep G ((A).S.side i per)}
    (course:Concourse R.alloy R.kit R.T π Γ b N per k H)(early:b≤j)(live:j<N)
    {d:ℕ}(grade:d≤Burn.horizon k):
    ((A).budget j).threshold^2*|(R.T.history N per j).beta-forecast R Γ N per j k|≤
      (2*ConnectedActivityE6.Coat.gStep (R.T.history N per j).beta)^(d+2):=by
  let x:ℝ:=(A).clock.hatBeta j
  let β:ℝ:=(R.T.history N per j).beta
  let P:=(A).budget j
  have band:β∈RG.Shoot.band (A) j:=((R.T.sticks N per).prices j (Nat.zero_le _) live.le).2
  have hx:1<x:=(A).fits.delayed j
  have hv:(2:ℝ)*Time.credit G (R.metals.p.profile ((A).clock.J j))≤1:=by
    linarith only [(Time.authorized G (R.metals.p.profile ((A).clock.J j))).1]
  have saved:=course.1.pace j early live
  have principal:P.threshold^2*|β-forecast R Γ N per j k|≤Burn.young x k:=by
    apply saved.trans
    change 2*(Time.credit G (R.metals.p.profile ((A).clock.J j))*Burn.young x k)≤Burn.young x k
    rw [←mul_assoc]
    exact mul_le_of_le_one_left (Real.rpow_nonneg (zero_le_one.trans hx.le) _) hv
  have paid:=band_gap x β (zero_lt_one.trans hx) (trial_in band)
  apply principal.trans ((young hx k d grade).trans ?_)
  apply pow_le_pow_left₀ (Clock.gp (zero_lt_one.trans hx)).le
  change Clock.gap x≤2*Clock.gap β
  linarith only [paid.1]

theorem original {N b j per k:ℕ}{π:ℕ→Layout G}{Γ:ℕ→Pace.Coin}
    {H:(i:ℕ)→RG.Rep G ((A).S.side i per)}
    (course:Concourse R.alloy R.kit R.T π Γ b N per k H)(early:b≤j)(live:j<N)
    {d:ℕ}(grade:d≤Burn.horizon k):
    |(R.T.history N per j).beta-forecast R Γ N per j k|≤
      2^(d+4)*ConnectedActivityE6.Coat.gStep (R.T.history N per j).beta^d:=by
  let x:ℝ:=(A).clock.hatBeta j
  let β:ℝ:=(R.T.history N per j).beta
  let g:=ConnectedActivityE6.Coat.gStep β
  let t:=((A).budget j).threshold
  have band:β∈RG.Shoot.band (A) j:=((R.T.sticks N per).prices j (Nat.zero_le _) live.le).2
  have hx:0<x:=zero_lt_one.trans ((A).fits.delayed j)
  have paid:=band_gap x β hx (trial_in band)
  have mon:1≤(A).clock.monitor j:=Real.one_le_exp (sq_nonneg _)
  have small:g≤2*t:=by
    refine paid.2.trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
    change Clock.gap x≤Clock.gap x*(A).clock.monitor j
    exact le_mul_of_one_le_right (Clock.gp hx).le mon
  have gp:0<g:=by
    have lower:x/4≤β:=(trial_in band).1
    have pos:0<β:=lt_of_lt_of_le (by positivity) lower
    exact inv_pos.mpr (Real.sqrt_pos.2 pos)
  let diff:=|β-forecast R Γ N per j k|
  have scaled:t^2*diff≤(2*g)^(d+2):=threshold R course early live grade
  have half:g/2≤t:=by linarith only [small]
  have stable:(g/2)^2*diff≤(2*g)^(d+2):=
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) half 2) (abs_nonneg _)).trans scaled
  change diff≤2^(d+4)*g^d
  apply (mul_le_mul_iff_right₀ (show 0<(g/2)^2 by positivity)).mp
  calc
    (g/2)^2*diff ≤ (2*g)^(d+2):=stable
    _ = (g/2)^2*(2^(d+4)*g^d):=by rw [mul_pow,pow_add,pow_add,pow_add];ring

end YM.Integration.WilsonVacuumPreResetTorusScalarClock
