import YM.Integration.WilsonVacuumPreResetTorusRegradedAction
import YM.Integration.WilsonVacuumPreResetTorusCoverAction

/-! The measured run's paid deposited layouts work for every stem side,
centered pair of test fields and retained grade before taking the fixed-top
copied-torus limit. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetTorusFundedMassLimit
open Function Filter Finset Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree MeasureTheory
open ConnectedActivityE6 ConnectedActivityE6.Coat
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure
open Bloch Laurent RG.Supply Extra.Histories GapsLocal.Renew
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Opera
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Physical WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV.Bank.Bloom WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Power WilsonCoeffUV.Embroider WilsonCoeffUV.Soil
open WilsonCoeffUV.Fk Next.Foundations WilsonLimitConstruction WilsonStartup PowerSeries
open scoped Topology BigOperators Classical
open WilsonVacuumPreResetTorusSeason
variable {G:Gauge}(R:Run G)


open AllOrder AllOrder.Ker AllOrder.Floe AllOrder.Floe.Step
open Primitives.TwoWave Primitives.TwoWave.RealSlice
open WilsonVacuumPreResetTorusGrade (evaluated)
open WilsonVacuumPreResetTorusActionRead (originalAction)
open WilsonVacuumPreResetTorusCoverAction (Cover sheets)
open FVA1Physical.TwoReset (coverFilter coverWin)
open scoped Classical

theorem original (simple:G.Simple)(held:WilsonFundedWindowCompany.PhysicalInputs R.kit)
    (mark:Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay)
    (checkoutPrice:Mallow.RG12.Earned (checkout G) R.kit.shape R.alloy.delay)(d:ℕ)
    (v:ℕ→Gear G→ℝ)(rows:FundedMarkedCoverRows.prices v R.kit)
    (paths:FundedOriginalVacuumPaths.prices R.kit)(e:ℕ):
    ∃ credit:Credit,∀ᶠ m:ℕ in atTop,
      let A:=R.family.path.levels
      ∃σ:ℝ,0<σ ∧ σ⁻¹≤zz A (m+1) ∧ ∀N:ℕ,m+1<N→
        let j:=m+1
        let C:=credit.buy (zz A j)+zz A j*A.clock.loopCap j
        let K:=R.alloy.B.kin.path N j
        let B:=(A.params j).clip
        let p:=pitch A R.metals.O N j
        ∃Z:SeriesA G,(∀a∈Z,3≤a.grade) ∧ fromBefore Z (3+e) ∧
          Z.length ≤ meterPre (3+e) ∧ Draw Z σ C ∧
          ∀t≤2+e,∀c:Side,∀z w:rule (Coarse G) c,
          let sold:=Pace.grouping (PertExtension.Series.Tested.term (p-1))
            (WilsonVacuumPreResetTorusDeposit.bank Z) (Step.tape (2+e)) B K t c
          Tendsto (fun v:Cover R j c=>(sheets R j c v:ℝ)⁻¹ •
            ((evaluated (originalAction R N j (R.family.side j v.val)) t (convey (coverWin v.prop) z)-
              evaluated (originalAction R N j (R.family.side j v.val)) t (convey (coverWin v.prop) w):ℝ):ℂ))
            (coverFilter R.family.S j c) (𝓝 ((sold z-sold w:ℝ):ℂ)):=by
  obtain ⟨credit,pricing⟩:=WilsonVacuumPreResetTorusSeasonFiled.original R simple held mark
    checkoutPrice d v rows paths e
  refine ⟨credit,?_⟩
  filter_upwards [pricing] with m layer
  obtain ⟨σ,positive,paid,produce⟩:=layer
  refine ⟨σ,positive,paid,?_⟩
  intro N older
  obtain ⟨Z,legal,grade,size,price,_,filed,_⟩:=produce N older
  refine ⟨Z,legal,grade,size,price,?_⟩
  intro t test c z w
  have proper:LocalRatio R.metals.O:=(RunFormalChain.fromRun R).receipt
  have unit:=Bank.angle_tilt (A:=R.family.path.levels) simple proper older
  have link (x:rule (Coarse G) c):=WilsonVacuumPreResetTorusRegradedAction.original
    _ unit (R.alloy.B.kin.path N (m+1)) (R.family.path.levels.params (m+1)).clip
    Z positive price legal test x
  dsimp only
  rw [link z,link w]
  exact WilsonVacuumPreResetTorusCoverAction.original R simple older Z c
    (filed t (by omega) c) z w

end YM.Integration.WilsonVacuumPreResetTorusFundedMassLimit
