import YM.Integration.WilsonVacuumPreResetTorusSeason
import YM.Integration.WilsonPhysicalHistoryRetainedSpringMeasured

/-! Compare an independently evolved cutoff tensor to the very corrected
original upper catalogue issued before every physical period. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetTorusSeasonFiled
open LocalComparison Marker Global FullQLocal Comparison.RG02 Comparison.RG02.Assembly
open IterationFour IterationFour.Vacuum
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

theorem priced (simple:G.Simple){j N e:ℕ}(older:j<N)(Z:SeriesA G)
    (sold:∀i<3+e,∀ n:Side,∀l,
      Blue.mix (pace (pitch R.family.path.levels R.metals.O N j))
        (front (R.alloy.B.kin.path N j) (R.family.path.levels.params j).clip n+sands Z n) i (l+1)=
        lagoon (freshet R.family.path.levels R.metals.O N j i (l+1)) n)
    {i:ℕ}(entry:i<3+e)(l:ℕ)(x:Fin (l+1)→YForest G):
    Tendsto (fun per=>
      let n:=R.family.side j per
      let pins:=foldUnder n ∘ x
      source R N j i (l+1) n pins-
        Blue.mix (pace (pitch R.family.path.levels R.metals.O N j))
          (front (R.alloy.B.kin.path N j) (R.family.path.levels.params j).clip n+sands Z n) i (l+1) pins)
      atTop (𝓝 0):=by
  apply (corrected R simple older i l x).congr'
  apply Eventually.of_forall fun per=>?_
  dsimp only
  rw [sold i entry]
  rfl

theorem original (simple:G.Simple)(held:WilsonFundedWindowCompany.PhysicalInputs R.kit)
    (mark:Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay)
    (checkoutPrice:Mallow.RG12.Earned (checkout G) R.kit.shape R.alloy.delay)(d:ℕ)
    (v:ℕ→Gear G→ℝ)(rows:FundedMarkedCoverRows.prices v R.kit)
    (paths:FundedOriginalVacuumPaths.prices R.kit)(e:ℕ):
    ∃ credit:Credit,∀ᶠ m:ℕ in atTop,
    let A:=R.family.path.levels
    ∃σ:ℝ,0<σ ∧ σ⁻¹≤zz A (m+1) ∧ ∀N:ℕ,(m+1<N) →
      let j:=m+1
      let C:=credit.buy (zz A j)+zz A j*A.clock.loopCap j
      let K:=R.alloy.B.kin.path N j
      let B:=(A.params j).clip
      ∃Z:SeriesA G,(∀a∈Z,3≤a.grade) ∧ fromBefore Z (3+e) ∧ Z.length ≤ meterPre (3+e) ∧
        Draw Z σ C ∧ RunFundedPeriodAction.PeriodData Z (2+e) σ C ∧
        (∀i<3+e,∀n:Side,∀l,Blue.mix (pace (pitch A R.metals.O N j))
          (front K B n+sands Z n) i (l+1)=lagoon (freshet A R.metals.O N j i (l+1)) n) ∧
        ∀i<3+e,∀l,∀x:Fin (l+1)→YForest G,
          Tendsto (fun per=>let n:=R.family.side j per
              source R N j i (l+1) n (foldUnder n ∘ x)-
              Blue.mix (pace (pitch A R.metals.O N j)) (front K B n+sands Z n)
                i (l+1) (foldUnder n ∘ x)) atTop (𝓝 0):=by
  obtain ⟨credit,issued⟩:=OriginalMarkedRunAction.cofinal_filed R simple held mark checkoutPrice d v rows paths e
  refine ⟨credit,?_⟩
  filter_upwards [issued] with m real
  obtain ⟨σ,pos,width,allDates⟩:=real
  refine ⟨σ,pos,width,?_⟩
  intro N earlier
  obtain ⟨Z,grade,valid,slots,listed,bank,genuine,_⟩:=allDates N earlier
  exact ⟨Z,grade,valid,slots,listed,bank,genuine,fun i hi l x=>priced R simple earlier Z genuine hi l x⟩

end YM.Integration.WilsonVacuumPreResetTorusSeasonFiled
