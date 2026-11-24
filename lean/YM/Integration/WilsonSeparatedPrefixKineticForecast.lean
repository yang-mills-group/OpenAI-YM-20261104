import YM.Integration.WilsonVacuumPreResetIndependentForecast
import YM.Integration.WilsonReportingAbsoluteInletForecastBooks

/-! The cover Hessian evaluated at the original finer coupling predicts the actual
coarser inverse temperature.  The same dated unmarked bank serves every period. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixKineticForecast
open Function Filter Finset Lattice Wilson RG RG.Supply Pressure Input Org Precision Tree
open Next.Scheduling Next.Scheduling.Clock AnalyticBridge VerifiedReset ConnectedActivityE6 PhysicalNext Repeat
open Progress.DirectedRecipe Payments Push AbsoluteSums PriceCompiler
open AllOrder AllOrder.Transit WheelP AllOrder.Floe AllOrder.Floe.Step PlanV Pane ThroughLaunch
open Roost Legato Graces Extra.Iteration Extra.Histories QuadraticLocal
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Blue WilsonCoeffUV.Mer
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark PowerSeries PertExtension.Series Pert.Asymptotics
open WilsonCoeffUV.Winding WilsonCoeffUV.Embroider WilsonCoeffUV.Power WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Power.Roam
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Bank.Mosaic
open WilsonVacuumPreResetStationaryChange WilsonVacuumPreResetDepositedRay WilsonVacuumPreResetOriginalOutput Marker Multi
open Next.Free FormalBulk08.Lotus FormalBulk08.Mesa FormalBulk08 FormalBulk08.Flat FormalBulk08.Reef FormalBulk08.Roof
open WilsonVacuumPreResetTorusScalarClock (forecast)
open WilsonVacuumPreResetDatedDeposit (Issued)
open WilsonVacuumPreResetMeasuredCoin (Agrees)
open WilsonReportingAbsoluteInletForecastBooks (value)
open private head from YM.Integration.WilsonReportingAbsoluteInletForecastBooks
open scoped Topology BigOperators Classical
variable {G:Gauge}(R:Run G)
local notation "V" => R.family.path.levels
local notation "g" => regulatorRun R.family
local notation "A" => R.alloy.B.a

def thermal (k N per j:ℕ):ℝ:=(R.T.history N per (j+1)).beta *
  value (Burn.horizon k+2) (pitch V R.metals.O N j) (g N per (j+1))

private theorem chart (u:G.ColorIndex)(simple:G.Simple)(v:ℕ→Gear G→ℝ)
    (rows:FundedMarkedCoverRows.prices v R.kit){N j:ℕ}(live:j<N)(k per:ℕ):
    forecast R (WilsonVacuumPreResetIndependentForecast.coin R u N) N per j k=thermal R k N per j:=by
  rw [forecast,←WilsonVacuumPreResetIndependentForecast.coin_eq R u simple v rows live]
  let x:=g N per (j+1)
  let H:=pitch V R.metals.O N j
  let n:=Burn.horizon k+2
  change _*(1+∑i∈range (n+1), x^i*(PowerSeries.coeff i (H-1)))=_*value n H x
  congr 1
  simp only [map_sub,mul_sub,Finset.sum_sub_distrib]
  change 1+(value n H x-value n 1 x)=value n H x
  rw [head];ring

theorem original (u:G.ColorIndex)(simple:G.Simple)(v:ℕ→Gear G→ℝ)(rows:FundedMarkedCoverRows.prices v R.kit)
    (paths:FundedOriginalVacuumPaths.prices R.kit)(k q:ℕ)(paid:q+1≤Burn.horizon k){ε:ℝ}(eps:0<ε):
    ∃W:Credit,∀ᶠ m:ℕ in atTop,∀N:ℕ,m≤N→∃Z:ℕ→SeriesA G,
      (∀j,m≤j→j≤N→∃σ:ℝ,0<σ ∧ σ⁻¹≤zz V j ∧
        Issued R N j (Burn.horizon k) (Z j) σ (W.buy (zz V j)+zz V j*(V).clock.loopCap j)) ∧
      ∀(D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)(Q:D.Tab R.rolls),
        TicketP R.alloy R.kit D Q→∀(π:ℕ→Layout G)(Γ:ℕ→Pace.Coin),
        PlanV.Path D R.alloy Q (Burn.horizon k) N m π Γ→Agrees R N m (Burn.horizon k) Z π Γ ∧
        ∀per (H:(i:ℕ)→RG.Rep G ((A).S.side i per)),Concourse R.alloy R.kit R.T π Γ m N per k H→
        ∀j,m≤j→j<N→let β:=(R.T.history N per j).beta
                     let B:=thermal R k N per j
                     0<B ∧ |β-B|≤ε*(g N per j)^q ∧ |β/B-1|≤ε*(g N per j)^(q+2) ∧
                       |Coat.gStep B/(g N per j)-1|≤ε*(g N per j)^(q+2):=by
  obtain ⟨W,market⟩:=WilsonVacuumPreResetIndependentForecast.original R u simple v rows paths k q paid eps
  refine ⟨W,?_⟩
  filter_upwards [market] with m before N live
  obtain ⟨Z,issued,hearing⟩:=before N live
  refine ⟨Z,issued,?_⟩
  intro D Q money π Γ path
  obtain ⟨agrees,_,reading⟩:=hearing D Q money π Γ path
  refine ⟨agrees,?_⟩
  intro per H course j mj jn
  dsimp only
  rw [←chart R u simple v rows jn k per]
  exact reading per H course j mj jn

end YM.Integration.WilsonSeparatedPrefixKineticForecast
end
