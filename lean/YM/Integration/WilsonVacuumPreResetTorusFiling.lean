import YM.Integration.WilsonVacuumPreResetTorusStock
import YM.AllOrder.Floe.Cascade

/-! The nominal Wilson action of the entered physical age tape on its actual
torus. Multiplication by the one common s² clears every Laurent channel. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetTorusFiling
open Filter Lattice Wilson RG PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Org Push.PriceCompiler AllOrder AllOrder.Floe AllOrder.Floe.Step
open AllOrder.Transit AllOrder.Transit.WheelP AllOrder.Till Extra.Iteration
open AnalyticBridge VerifiedReset ConnectedActivityE6 Stationary
open Primitives.TwoWave Primitives.TwoWave.RealSlice Haiku
open Pressure Response Ink Ink.Method Ink.Money Laurent
open PertExtension.Series Radial PositionX.Jet AllOrder.Laplace.SigmaP Push.AbsoluteSums
open scoped BigOperators Classical Topology ContDiff
variable {G:Gauge}

def clipped (π:Layout G)(b:ℕ):Layout G:=fun i=>legible (π i) b

def arm (π:Layout G)(i:Age){n:Side}(u:Stationary.Link G n)(s:ℝ):ℝ:=
  s^i.stamp * turnSeries (π i) (s•u)

def issued (π:Layout G)(k:ℕ){n:Side}(u:Stationary.Link G n)(s:ℝ):ℝ:=
  ∑i∈Age.scope (Burn.horizon k+2),arm π i u s

theorem deployed (B:BudgetPoint)(π:Layout G)(k:ℕ)(n:Side)(u:Stationary.Link G n)
    (s:ℝ)(hot:0<s)(room:4*(Burn.horizon k+4)≤B.B):
    s^2*(∑ x:Site n,M0 k 0 B π ((s^2)⁻¹) n x (Stationary.input G n (s•u))) =
      issued (clipped π B.B) k u s:=by
  let β:ℝ:=(s^2)⁻¹
  have cancel:s^2*β=1:=mul_inv_cancel₀ (pow_ne_zero 2 hot.ne')
  have regulator:Coat.gStep β=s:=by
    change (Real.sqrt ((s^2)⁻¹))⁻¹=s
    rw [Real.sqrt_inv,Real.sqrt_sq hot.le,inv_inv]
  have fits:∀i∈Age.scope (Burn.horizon k+2),4*i.r≤B.B:=by
    intro i live
    have hi:=Age.in_scope.mp live
    have hr:=i.pricey
    omega
  let U:=Stationary.input G n (s•u)
  have book:= (Tilt.sunset π _ B.B fits s hot β cancel U).symm
  change s^2*(∑x:Site n,Tilt.patch G B.B n x (Age.scope (Burn.horizon k+2)) π
    (Coat.gStep β) U) = _
  rw [regulator,book,←mul_assoc,cancel,one_mul]
  rfl

theorem filed (π:Layout G)(i:Age)(n:Side)(u:Stationary.Link G n)
    {width C:ℝ}(warm:0<width)(store:SumBudget (fun b=>(π i b).budget width) C)
    (t:ℕ):someJ (arm π i u) (t+2)=Haiku.Coat.trade i.e (π i) t n u:=by
  let f:=turnSeries (π i) (m:=n)
  have fine:AnalyticAt ℝ f 0:=turns_analytic _ warm store
  have along:ContDiffAt ℝ ω (fun s:ℝ=>f (s•u)) 0:=by
    have ray:ContDiff ℝ ω (fun s:ℝ=>s•u):=by fun_prop
    have at0:ContDiffAt ℝ ω f ((fun s:ℝ=>s•u) 0):=by
      simpa using (show ContDiffAt ℝ ω f 0 from fine.contDiffAt)
    change ContDiffAt ℝ ω (f ∘ (fun s:ℝ=>s•u)) 0
    exact at0.comp (0:ℝ) ray.contDiffAt
  have release:=dispersal (fun s:ℝ=>f (s•u)) along 1 (t+2) i.stamp
  have raw:someJ (arm π i u) (t+2)=if i.stamp≤t+2 then
      Radial.jet f (t+2-i.stamp) u else 0:=by
    change someJ (fun s:ℝ=>s^i.stamp*f (s•u)) (t+2)=_
    simpa only [one_mul,one_pow,jet_entry (fine.contDiffAt.of_le le_top) u] using release
  rw [raw]
  unfold Haiku.Coat.trade
  have age:=i.recovery
  by_cases active:i.e≤t
  · rw [if_pos active,if_pos (by omega)]
    congr 2
    omega
  · rw [if_neg active]
    by_cases fits:i.stamp≤t+2
    · rw [if_pos fits]
      have low:(t+2-i.stamp) < i.r:=by omega
      have zero:= (rays_jet fine i.r).1 (turns_low (m:=n) (π i) warm store) _ low
      rw [Radial.jet,zero]
      simp
    · rw [if_neg fits]
      rfl

end YM.Integration.WilsonVacuumPreResetTorusFiling
