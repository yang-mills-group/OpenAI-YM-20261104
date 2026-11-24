import YM.Integration.WilsonVacuumPreResetFoldedCopyRead
import YM.Integration.FVA1Physical.TwoReset.VacuumCover

/-! The original two-reset mass call at an interior deposited date. Both galleries precede the period. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetMassCall
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

open WilsonCoeffUV.Winding
open Comparison.RG02 Next.SectorChange Marker Exterior
open WilsonVacuumPreResetTorusDeposit (bank)
open FVA1Physical.TwoReset (MassCall coveringVac)

theorem binding (simple:G.Simple){N j e:ℕ}(hj:j<N)(low upper:SeriesA G)
    (price:∀l≤e+2,∀X:Side,∀x y:rule (Coarse G) X,
      let A:=R.family.path.levels
      let sold:=Pace.grouping (PertExtension.Series.Tested.term (pitch A R.metals.O N j-1))
          (bank low) (Step.tape (e+2)) (A.params j).clip (R.alloy.B.kin.path N j) l X
      Tendsto (fun v:Cover R j X=>(sheets R j X v:ℝ)⁻¹ •
        ((evaluated (originalAction R N j (R.family.side j v.val)) l (convey (coverWin v.prop) x)-
          evaluated (originalAction R N j (R.family.side j v.val)) l (convey (coverWin v.prop) y):ℝ):ℂ))
        (coverFilter R.family.S j X) (𝓝 ((sold x-sold y:ℝ):ℂ)))
    (physical:∀(p:ℕ)(F:Forest (WilsonVacuumPreResetStationaryChange.step R j p).ratio)
      (tag:(WilsonVacuumPreResetStationaryChange.step R j p).Choices)
      {V:Type} [DecidableEq V] [Fintype V] {J:Census V}
      (U:Bulk.Colors J G (R.family.side (j+1) p))
      (x y:Exterior.fieldDir G (R.family.side j p) 1)(l:ℕ)(_read:l≤e+2)(h:j<N),
       WilsonVacuumPreResetOriginalOutput.held R N j p h F tag upper U (e+2) x (e+2) l-
       WilsonVacuumPreResetOriginalOutput.held R N j p h F tag upper U (e+2) y (e+2) l=
       -(WilsonVacuumPreResetOriginalOutput.diff (WilsonVacuumPreResetOriginalOutput.output R N j p) l
            (FreeResolvent.flatten x) (FreeResolvent.flatten y):ℂ)):
    let A:=R.family.path.levels
    MassCall R hj (bank upper) (bank low) (PertExtension.Series.Tested.term (pitch A R.metals.O N j-1)) e:=by
  intro A V _ _ J X U Y tag l hl x
  have money:=price l (by omega) X x 0
  have change:=WilsonVacuumPreResetFoldedCopyRead.original R simple hj l X x 0
  dsimp only at change money
  have endpt:=(change.add money).neg
  rw [zero_add] at endpt
  apply endpt.congr' (Eventually.of_forall ?_)
  intro v
  let y:=Stationary.arm G _ 1 (convey (coverWin v.prop) x)
  let y₀:=Stationary.arm G _ 1 (convey (coverWin v.prop) (0:rule (Coarse G) X))
  have actual:=physical v.val (Y v) (tag v) (U v) y y₀ l hl hj
  let S:=sheets R j X v
  let n:=R.family.side j v.val
  let F:=coil0 A R.metals.O j N n
  let T:=originalAction R N j n
  let z:=convey (coverWin v.prop) x
  let w:=convey (coverWin v.prop) (0:rule (Coarse G) X)
  let dF:ℝ:=evaluated F l z-evaluated F l w
  let dT:ℝ:=evaluated T l z-evaluated T l w
  change -((S:ℝ)⁻¹ • (((dF-dT:ℝ):ℂ))+(S:ℝ)⁻¹ • (dT:ℂ))=
    (S:ℝ)⁻¹ • _-(S:ℝ)⁻¹ • _
  rw [←smul_sub]
  change -((S:ℝ)⁻¹ • (((dF-dT:ℝ):ℂ))+(S:ℝ)⁻¹ • (dT:ℂ))=
    (S:ℝ)⁻¹ • (WilsonVacuumPreResetOriginalOutput.held R N j v.val hj (Y v) (tag v) upper (U v) (e+2) y (e+2) l-
      WilsonVacuumPreResetOriginalOutput.held R N j v.val hj (Y v) (tag v) upper (U v) (e+2) y₀ (e+2) l)
  rw [actual]
  change -((S:ℝ)⁻¹ • (((dF-dT:ℝ):ℂ))+(S:ℝ)⁻¹ • (dT:ℂ))=(S:ℝ)⁻¹ • -(dF:ℂ)
  rw [Complex.ofReal_sub,smul_sub,sub_add_cancel,smul_neg]


theorem original (simple:G.Simple)(held:WilsonFundedWindowCompany.PhysicalInputs R.kit)
    (mark:Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay)
    (checkoutPrice:Mallow.RG12.Earned (checkout G) R.kit.shape R.alloy.delay)(d:ℕ)
    (v:ℕ→Gear G→ℝ)(rows:FundedMarkedCoverRows.prices v R.kit)
    (paths:FundedOriginalVacuumPaths.prices R.kit)(e:ℕ):
    ∃ C₀ C₁:Credit,∀ᶠ m:ℕ in atTop,
      let A:=R.family.path.levels
      let j:=m+1
      ∃ σ₀ σ₁:ℝ,0<σ₀ ∧ σ₀⁻¹≤zz A j ∧ 0<σ₁ ∧ σ₁⁻¹≤zz A (j+1) ∧
      ∀ N (hj:j<N),∃ low upper:SeriesA G,
        (∀a∈low,3≤a.grade) ∧ fromBefore low (3+e) ∧ low.length ≤ meterPre (3+e) ∧
        Draw low σ₀ (C₀.buy (zz A j)+zz A j*A.clock.loopCap j) ∧
        (∀a∈upper,3≤a.grade) ∧ fromBefore upper (3+e) ∧ upper.length ≤ meterPre (3+e) ∧
        Draw upper σ₁ (C₁.buy (zz A (j+1))+zz A (j+1)*A.clock.loopCap (j+1)) ∧
        MassCall R hj (bank upper) (bank low) (PertExtension.Series.Tested.term (pitch A R.metals.O N j-1)) e:=by
  obtain ⟨C₀,lowDates⟩:=WilsonVacuumPreResetTorusFundedMassLimit.original R simple held mark
    checkoutPrice d v rows paths e
  obtain ⟨C₁,upperDates⟩:=WilsonVacuumPreResetFundedOutput.original R simple v rows paths e
  obtain ⟨m₀,lo⟩:=eventually_atTop.1 lowDates
  obtain ⟨m₁,up⟩:=eventually_atTop.1 upperDates
  refine ⟨C₀,C₁,eventually_atTop.2 ⟨max m₀ m₁,?_⟩⟩
  intro m hm A j
  obtain ⟨σ₀,hσ₀,k₀,pay₀⟩:=lo m (le_trans (le_max_left _ _) hm)
  obtain ⟨σ₁,hσ₁,k₁,pay₁⟩:=up j (le_trans (le_trans (le_max_right _ _) hm) (Nat.le_succ m))
  refine ⟨σ₀,σ₁,hσ₀,k₀,hσ₁,k₁,?_⟩
  intro N hj
  obtain ⟨low,l₀,l₁,l₂,l₃,price⟩:=pay₀ N hj
  obtain ⟨upper,u₀,u₁,u₂,u₃,physical⟩:=pay₁ N hj
  refine ⟨low,upper,l₀,l₁,l₂,l₃,u₀,u₁,u₂,u₃,?_⟩
  rw [show 2+e=e+2 by omega] at price
  exact binding R simple hj low upper price physical

end YM.Integration.WilsonVacuumPreResetMassCall
