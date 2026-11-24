import YM.Integration.WilsonVacuumPreResetTorusFiling

/-! The full submitted M0 at its actual prior, and the old course's honest
reset convolution on that same set of incoming ages. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetTorusNominal
open Filter Lattice Wilson RG PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Org Push.PriceCompiler AllOrder AllOrder.Floe AllOrder.Floe.Step
open AllOrder.Transit AllOrder.Transit.WheelP AllOrder.Till Extra.Iteration
open AnalyticBridge VerifiedReset ConnectedActivityE6 Stationary RG.Supply
open Haiku PositionX.Jet Push.AbsoluteSums Finset
open WilsonVacuumPreResetTorusFiling
open scoped BigOperators Classical Topology ContDiff
variable {G:Gauge}

def Purchased (π:Layout G)(k:ℕ):Prop:=
  ∀a∈Age.scope (Burn.horizon k+2),∃σ C:ℝ,0<σ ∧ Charged (π a) σ C

theorem dated (R:Run G){r:PlanV.Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel}
    {Q:r.Tab R.rolls}{π:ℕ→Layout G}{Γ:ℕ→Pace.Coin}{m N j k:ℕ}
    (route:PlanV.Path r R.alloy Q (Burn.horizon k) N m π Γ)(early:m≤j)(late:j≤N):
    Purchased (π j) k ∧ Purchased (clipped (π j) (R.alloy.B.a.budget j).B) k:=by
  have bought:Purchased (π j) k:=by
    intro a active
    exact ⟨_,_,(r.shape _).pos (R.alloy.B.a.clock.J j) a,(route.1 j early late a active).pay⟩
  refine ⟨bought,fun a live=>?_⟩
  obtain ⟨σ,C,warm,pay⟩:=bought a live
  exact ⟨σ,C,warm,leg_pays _ pay warm _⟩

private theorem smooth (π:Layout G)(a:Age){n:Side}(u:Stationary.Link G n)
    {σ C:ℝ}(warm:0<σ)(pay:Charged (π a) σ C):ContDiffAt ℝ ω (arm π a u) 0:=by
  let f:=turnSeries (π a) (m:=n)
  have ray:ContDiff ℝ ω (fun s:ℝ=>s•u):=by fun_prop
  have outer:ContDiffAt ℝ ω f ((fun s:ℝ=>s•u) 0):=by
    simpa using (show ContDiffAt ℝ ω f 0 from (turns_analytic _ warm pay).contDiffAt)
  have comp:ContDiffAt ℝ ω (f∘(fun s:ℝ=>s•u)) 0:=outer.comp (0:ℝ) ray.contDiffAt
  exact (contDiffAt_id.pow a.stamp).mul comp

theorem summed (π:Layout G){k:ℕ}(pay:Purchased π k)(n:Side)(u:Stationary.Link G n)(t:ℕ):
    someJ (issued π k u) (t+2) =
    ∑a∈Age.scope (Burn.horizon k+2),Haiku.Coat.trade a.e (π a) t n u:=by
  have charges a (mem:a∈Age.scope (Burn.horizon k+2)):ContDiffAt ℝ (↑(t+2:ℕ)) (arm π a u) 0:=by
    obtain ⟨σ,C,warm,funded⟩:=pay a mem
    exact (smooth π a u warm funded).of_le le_top
  change ((t+2).factorial:ℝ)⁻¹ • iteratedDeriv (t+2)
    (fun s=>∑a∈Age.scope (Burn.horizon k+2),arm π a u s) 0=_
  rw [iteratedDeriv_fun_sum charges,smul_sum]
  apply sum_congr rfl
  intro a live
  obtain ⟨σ,C,warm,amount⟩:=pay a live
  exact filed π a n u warm amount t

theorem reset (π:Layout G){k:ℕ}(pay:Purchased π k)(q:Pace.Coin)
    (n:Side)(u:Stationary.Link G n)(t:ℕ):
    Pace.glory q π (Age.scope (Burn.horizon k+2)) t n u =
    ∑a∈Age.scope (Burn.horizon k+2),∑v∈range (t+1),
      Pace.ladder (Pace.elapsed a) q v * someJ (arm π a u) (t-v+2):=by
  unfold Pace.glory
  simp only [Finset.sum_apply]
  apply sum_congr rfl
  intro a live
  obtain ⟨σ,C,warm,amount⟩:=pay a live
  unfold Pace.moiety
  rw [Pace.weighs]
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  apply sum_congr rfl
  intro v hv
  rw [filed π a n u warm amount (t-v)]

end YM.Integration.WilsonVacuumPreResetTorusNominal
