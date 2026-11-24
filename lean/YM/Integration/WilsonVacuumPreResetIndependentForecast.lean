import YM.Integration.WilsonVacuumPreResetIndependentHistory
import YM.Integration.WilsonVacuumPreResetMeasuredBeta
import YM.Integration.WilsonVacuumPreResetMeasuredCaliber

/-! The independent curvature prescription reads and predicts the measured coupling on the original course. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetIndependentForecast
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

open Primitives.TwoWave.RealSlice PertExtension.Series
open Next.Free FormalBulk08.Lotus FormalBulk08.Mesa
open FormalBulk08 FormalBulk08.Flat FormalBulk08.Reef FormalBulk08.Roof
open WilsonVacuumPreResetDatedDeposit (Issued)
open WilsonVacuumPreResetMeasuredCoin (Agrees)


variable (u:G.ColorIndex)
local notation "V" => R.family.path.levels
set_option quotPrecheck false in
local notation "wood" => (fun j:ℕ=>Flat.routes (R.family.path.levels.clock.op j 0).patch)
set_option quotPrecheck false in
local notation "branches" => (fun j:ℕ=>(R.family.path.levels.blocks j 0).branches)

noncomputable abbrev prescription (N j:ℕ):PowerSeries ℝ:=
  Roof.epoch u (destination V N j) (wood j) (V).clock.kernel
    (Dove.model V wood branches R.metals.O u N (j+1)) R.metals.O (branches j)

noncomputable abbrev coin (N j:ℕ):Pace.Coin:=Tested.term (prescription R u N j-1)

theorem pitch_eq (simple:G.Simple)(v:ℕ→Gear G→ℝ)(rows:FundedMarkedCoverRows.prices v R.kit)
    {N j:ℕ}(live:j<N):pitch V R.metals.O N j=prescription R u N j:=by
  have tags:∀i n,(primary (R.family.path.levels.clock.op i 0).patch R.family.path.levels.clock.kernel n).Choices:=
    fun _ _=>Classical.choice inferInstance
  exact ((WilsonVacuumPreResetIndependentHistory.original R u simple v rows tags N j live.le).2 live).2

theorem coin_eq (simple:G.Simple)(v:ℕ→Gear G→ℝ)(rows:FundedMarkedCoverRows.prices v R.kit)
    {N j:ℕ}(live:j<N):WilsonVacuumPreResetDatedCourse.coin R N j=coin R u N j:=by
  exact congrArg (fun X:PowerSeries ℝ=>Tested.term (X-1)) (pitch_eq R u simple v rows live)

theorem original (simple:G.Simple)(v:ℕ→Gear G→ℝ)(rows:FundedMarkedCoverRows.prices v R.kit)
    (paths:FundedOriginalVacuumPaths.prices R.kit)(k q:ℕ)(paid:q+1≤Burn.horizon k){ε:ℝ}(eps:0<ε):
    ∃W:Credit,∀ᶠ m:ℕ in atTop,∀N:ℕ,m≤N→∃Z:ℕ→SeriesA G,
      (∀j,m≤j→j≤N→∃σ:ℝ,0<σ ∧ σ⁻¹≤zz (levels R) j ∧
        Issued R N j (Burn.horizon k) (Z j) σ (W.buy (zz (levels R) j)+zz (levels R) j*(levels R).clock.loopCap j)) ∧
      ∀(D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)(Q:D.Tab R.rolls),
        TicketP R.alloy R.kit D Q→∀(π:ℕ→Layout G)(Γ:ℕ→Pace.Coin),
        PlanV.Path D R.alloy Q (Burn.horizon k) N m π Γ→Agrees R N m (Burn.horizon k) Z π Γ ∧
        (∀j,m≤j→j<N→∀l≤Burn.horizon k+2,Γ j l=coin R u N j l) ∧
        ∀per (H:(i:ℕ)→Rep G ((A).S.side i per)),Concourse R.alloy R.kit R.T π Γ m N per k H→
        ∀j,m≤j→j<N→let β:=(R.T.history N per j).beta
                     let B:=forecast R (coin R u N) N per j k
                     let g:=Coat.gStep β
                     0<B ∧ |β-B|≤ε*g^q ∧ |β/B-1|≤ε*g^(q+2) ∧
                       |Coat.gStep B/g-1|≤ε*g^(q+2):=by
  obtain ⟨W,bought⟩:=WilsonVacuumPreResetMeasuredBeta.original R simple v rows paths k q paid eps
  refine ⟨W,?_⟩
  filter_upwards [bought] with m sale N past
  obtain ⟨Z,issued,whole⟩:=sale N past
  refine ⟨Z,issued,?_⟩
  intro D Q ticket π Γ path
  obtain ⟨agrees,rate⟩:=whole D Q ticket π Γ path
  refine ⟨agrees,fun j lo live l hl=>(agrees.rates j lo live l hl).trans
    (congrFun (coin_eq R u simple v rows live) l),?_⟩
  intro per H course j lo live
  have price:=rate per H course j lo live
  have same:forecast R (WilsonVacuumPreResetDatedCourse.coin R N) N per j k=
      forecast R (coin R u N) N per j k:=by
    unfold forecast
    rw [coin_eq R u simple v rows live]
  simpa only [same] using price

end YM.Integration.WilsonVacuumPreResetIndependentForecast
end
