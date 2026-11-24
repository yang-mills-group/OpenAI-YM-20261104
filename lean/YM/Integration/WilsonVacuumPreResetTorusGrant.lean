import YM.Integration.WilsonVacuumPreResetTorusNominal
import YM.Integration.WilsonVacuumPreResetTorusSites
import YM.QuadraticLocal.Fk.Vesper

/-! The genuine complete compact-field QuadraticLocal grant and the localized M0
at a nonbare incoming date, resolved on every real occurring age and site. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetTorusGrant
open Filter Lattice Wilson RG PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Org Push.PriceCompiler AllOrder AllOrder.Floe AllOrder.Floe.Step
open AllOrder.Transit AllOrder.Transit.WheelP AllOrder.Till Extra.Iteration
open AnalyticBridge VerifiedReset
open ConnectedActivityE6
open scoped BigOperators Classical Topology

open Precision RG.Supply
variable {G:Gauge}(R:Run G)
variable {r:PlanV.Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel}
variable {Q:r.Tab R.rolls}
set_option quotPrecheck false
local notation "V" => R.alloy.B.a



open AllOrder.Transit AllOrder.Transit.WheelP AllOrder.Till WilsonVacuumPreResetTorusSites

def balance (π:Layout G)(B:BudgetPoint)(a:Age){n:Side}(U:Config G n)(ρ:Signed)(x:Site n):ℝ:=
  site (π a) (pull ρ 0 U) x-site (legible (π a) B.B) (pull ρ 0 U) x

theorem issued (B:BudgetPoint)(π:Layout G)(k:ℕ)(n:Side)(U:Config G n)
    {β:ℝ}(healthy:0<β)(space:4*(Burn.horizon k+4)≤B.B):
    let s:=Coat.gStep β
    QuadraticLocal.Fk.money π (Age.scope (Burn.horizon k+2)) s U - s^2*∑x:Site n,M0 k 0 B π β n x U =
      ∑a∈Age.scope (Burn.horizon k+2),s^a.stamp*(Patch.average fun ρ:Signed=>∑x:Site n,balance π B a U ρ x):=by
  intro s
  have hot:0<s:=inv_pos.mpr (Real.sqrt_pos.mpr healthy)
  have scaling:s^2*β=1:=by
    change (Real.sqrt β)⁻¹^2*β=1
    rw [inv_pow,Real.sq_sqrt healthy.le,inv_mul_cancel₀ healthy.ne']
  have fits:∀i∈Age.scope (Burn.horizon k+2),4*i.r≤B.B:=by
    intro a live
    have:=Age.in_scope.mp live
    have:=a.pricey
    omega
  have retained:s^2*∑x:Site n,M0 k 0 B π β n x U =
      ∑a∈Age.scope (Burn.horizon k+2),s^a.stamp*Extra.Iteration.action (legible (π a) B.B) U:=by
    change s^2*(∑x:Site n,Tilt.patch G B.B n x (Age.scope (Burn.horizon k+2)) π s U)=_
    rw [←Tilt.sunset π _ B.B fits s hot β scaling U,←mul_assoc,scaling,one_mul]
  rw [retained]
  simp only [QuadraticLocal.Fk.money,Finset.sum_apply,AllOrder.Floe.sketch,Pi.smul_apply,smul_eq_mul]
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  rw [←mul_sub]
  congr 1
  unfold Extra.Iteration.action Patch.average Precision.uncut balance site
  simp only [Finset.sum_sub_distrib,mul_sub]

theorem posted {N b j k:ℕ}{π:ℕ→Layout G}{Γ:ℕ→Pace.Coin}
    (path:PlanV.Path r R.alloy Q (Burn.horizon k) N b π Γ)(first:b≤j)(last:j≤N)
    {a:Age}(bought:a∈Age.scope (Burn.horizon k+2)){n:Side}
    (U:Config G n)(ρ:Signed)(x:Site n):
    let σ:=r.pre (Burn.horizon k) (R.alloy.B.a.clock.J j) a
    let C:=PlanV.capprice R.alloy (Burn.horizon k) j a
    let B:=R.alloy.B.a.budget j
    |balance (π j) B a U ρ x|≤2*(Real.exp (-(σ/2)*B.B)*C)*2^a.r:=
  WilsonVacuumPreResetTorusSites.history R path first last a bought n (pull ρ 0 U) x

end YM.Integration.WilsonVacuumPreResetTorusGrant
