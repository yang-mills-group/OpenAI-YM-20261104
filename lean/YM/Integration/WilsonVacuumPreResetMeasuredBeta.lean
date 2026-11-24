import YM.Integration.WilsonVacuumPreResetMeasuredCoin
import YM.Integration.WilsonVacuumPreResetTorusScalarRatio

/-! A single measured PlanV course computes its kinetic reset at the actual upper inverse temperature. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetMeasuredBeta
open Function Filter Finset Lattice Wilson RG RG.Supply Pressure Input Org Precision Tree
open Next.Scheduling Next.Scheduling.Clock AnalyticBridge VerifiedReset ConnectedActivityE6 PhysicalNext Repeat
open Progress.DirectedRecipe Payments Push AbsoluteSums PriceCompiler
open AllOrder AllOrder.Transit WheelP AllOrder.Floe AllOrder.Floe.Step PlanV Pane ThroughLaunch
open Roost Legato Graces Extra.Iteration Extra.Histories
open QuadraticLocal
open scoped Topology BigOperators Classical
variable {G:Gauge}(R:Run G)
local notation "A" => R.alloy.B.a

open WilsonVacuumPreResetTorusScalarClock

open Function Filter Finset Lattice Laurent Bloch Wilson RG Precision Exterior Tree Matrix PowerSeries
open PhysicalNext.Repeat.Legato Comparison.RG02 FreeResolvent WilsonCoeffUV WilsonCoeffUV.Bank
open WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open WilsonCoeffUV.Winding WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Bank.Mosaic
open WilsonVacuumPreResetStationaryChange WilsonVacuumPreResetDepositedRay
open WilsonVacuumPreResetOriginalOutput Marker Multi

open WilsonVacuumPreResetDatedCourse (coin)
open WilsonVacuumPreResetDatedDeposit (Issued)
open WilsonVacuumPreResetMeasuredCoin (Agrees)


theorem forecast_eq {i N e:ℕ}{Γ:ℕ→Pace.Coin}(paid:∀l≤e,Γ i l=coin R N i l)(β:ℝ):
    Wheel.now (Γ i) e β=Wheel.now (coin R N i) e β:=by
  unfold Wheel.now Wheel.wag PositionX.Jet.delay
  congr 2
  apply Finset.sum_congr rfl
  intro k hk
  rw [paid k (by simpa using hk)]


theorem original (simple:G.Simple)(v:ℕ→Gear G→ℝ)(rows:FundedMarkedCoverRows.prices v R.kit)
    (paths:FundedOriginalVacuumPaths.prices R.kit)(k q:ℕ)(paid:q+1≤Burn.horizon k){ε:ℝ}(eps:0<ε):
    ∃W:Credit,∀ᶠ m:ℕ in atTop,∀N:ℕ,m≤N→∃Z:ℕ→SeriesA G,
      (∀j,m≤j→j≤N→∃σ:ℝ,0<σ ∧ σ⁻¹≤zz (levels R) j ∧
        Issued R N j (Burn.horizon k) (Z j) σ (W.buy (zz (levels R) j)+zz (levels R) j*(levels R).clock.loopCap j)) ∧
      ∀(D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)(Q:D.Tab R.rolls),
        TicketP R.alloy R.kit D Q→∀(π:ℕ→Layout G)(Γ:ℕ→Pace.Coin),
        PlanV.Path D R.alloy Q (Burn.horizon k) N m π Γ→Agrees R N m (Burn.horizon k) Z π Γ ∧
        ∀per (H:(i:ℕ)→Rep G ((A).S.side i per)),Concourse R.alloy R.kit R.T π Γ m N per k H→
        ∀j,m≤j→j<N→let β:=(R.T.history N per j).beta
                     let B:=forecast R (coin R N) N per j k
                     let g:=Coat.gStep β
                     0<B ∧ |β-B|≤ε*g^q ∧ |β/B-1|≤ε*g^(q+2) ∧
                       |Coat.gStep B/g-1|≤ε*g^(q+2):=by
  obtain ⟨W,banks⟩:=WilsonVacuumPreResetMeasuredCoin.original R simple v rows paths (Burn.horizon k)
  obtain ⟨j₀,amount⟩:=eventually_atTop.1 (WilsonVacuumPreResetTorusScalarRatio.original R simple q eps)
  refine ⟨W,?_⟩
  filter_upwards [banks,eventually_ge_atTop j₀] with m bank past
  intro N ordered
  obtain ⟨Z,quotes,_,book⟩:=bank N ordered
  refine ⟨Z,quotes,?_⟩
  intro D Q ticket π Γ path
  have aligned:=book D Q π Γ path ticket.pledge.formal
  refine ⟨aligned,?_⟩
  intro per H course j hj live
  have same:forecast R Γ N per j k=forecast R (coin R N) N per j k:=
    forecast_eq R (aligned.rates j hj live) _
  exact same ▸ amount j (past.trans hj) course hj live paid

end YM.Integration.WilsonVacuumPreResetMeasuredBeta
