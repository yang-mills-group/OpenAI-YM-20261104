import YM.Integration.WilsonPhysicalHistoryRetainedSpringLocalCourse
import YM.Integration.WilsonVacuumPreResetSameBilled

/-! The independent row price is paid at the genuine incoming temperature
and on the same positive representation kept by the local comparison. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.OriginalMarkedRunAction
open Filter Function Lattice RG Wilson WilsonStartup AnalyticBridge PhysicalNext PhysicalNext.Repeat Legato
open Pert.Asymptotics VerifiedReset RG01Estimate Time WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Physical WilsonLimitConstruction
open Collection Function Marker IterationFour.Vacuum Extra.Iteration Push Push.AbsoluteSums Push.AbsoluteSums.Animals Song Meadow
open WilsonVacuumPreResetRenderRank WilsonVacuumPreResetPeriodEntries
open scoped Topology BigOperators Classical
variable {G:Gauge}
theorem spring_model_bill (R:Run G)(simple:G.Simple)(v:ℕ→Gear G→ℝ)(rows:FundedMarkedCoverRows.prices v R.kit)
    (render:WilsonVacuumPreResetRenderCalendar.Issued R.kit)(income:WilsonVacuumPreResetPrecursorReserve.Issued R.kit)
    (time:RG01Estimate.Chart.Barrier R.alloy (fun _ i=>((i:ℝ)+1)⁻¹))(W:Credit)(r cap:ℕ){ε:ℝ}(ep:0<ε):
    let V:=R.family.path.levels
    ∀ᶠ j:ℕ in atTop,∀N per:ℕ,j<N→
      let C:=W.buy (zz V j)+zz V j*V.clock.loopCap j
      ∀(A:Listing G (R.family.side j per))(σ:ℝ)(Z:SeriesA G),0<σ→σ⁻¹≤zz V j→
        (∀a∈Z,3≤a.grade ∧ a.grade≤cap)→Z.length ≤ meterPre cap→∀t,
        |(maskedSpringModel R N per j r Z σ C A t).bill|≤ε*Time.forecastE V j:=by
  intro V
  filter_upwards [WilsonVacuumPreResetSameBilled.original R simple v rows render income time W r cap ep] with j pay N per live
  intro C A σ Z sp width grades length t
  let Y:=R.family.path.rep N per j
  have rep:=R.makes.wilson.represents N per j live.le
  have budget:Y.p=V.budget j:=rep.vac
  have held:RG.Shoot.Lives R.alloy.B.bake N j per Y:=((R.T.sticks N per).prices j (Nat.zero_le _) live.le).1
  have path:Y.path=R.alloy.B.kin.path N j:=by rw [held.path,R.alloy.B.bases]
  have correct:=pay N per live (R.family.side j per) A σ Z sp width grades length t (V.budget j).B
  unfold maskedSpringModel
  change |(WilsonVacuumPreResetModelBoard.source A Y.p Y.path _ _ _ _ _ σ C Z _ t Y.p.B).bill| ≤ _
  rw [budget,path]
  exact correct

end YM.Integration.OriginalMarkedRunAction
