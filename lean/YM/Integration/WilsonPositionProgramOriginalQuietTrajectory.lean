import YM.Integration.WilsonPositionProgramFullReceivingMass
import YM.Integration.WilsonSubmittedCalendar

/-! All filed vacuum grades on the measured Wilson route and the actual finite period. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPositionProgramOriginalQuietTrajectory
open Function Filter Finset Lattice Laurent Bloch Wilson RG Precision Exterior Tree Matrix PowerSeries
open PhysicalNext.Repeat.Legato Comparison.RG02 FreeResolvent WilsonCoeffUV WilsonCoeffUV.Bank
open WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open WilsonCoeffUV.Winding WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Bank.Mosaic
open WilsonVacuumPreResetStationaryChange WilsonVacuumPreResetDepositedRay
open WilsonVacuumPreResetOriginalOutput Marker Multi
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
attribute [local instance] Gauge.frobInner
variable {G:Gauge}(R:Run G)

open WilsonVacuumPreResetTorusDeposit (bank)
open WilsonVacuumPreResetTorusGrade (evaluated)
open FVA1Physical.TwoReset (MassCall)
open AllOrder.Floe.Step
open AllOrder.Ker Primitives.TwoWave.RealSlice


open WilsonVacuumPreResetDatedDeposit (Issued)
open WilsonVacuumPreResetMeasuredCoin (Agrees)
open WilsonVacuumPreResetDepositedGeometric (source)
open QuadraticLocal.Earn AllOrder.Floe

open WilsonFiledPeriodSeam WilsonCoeffUV.Bank.Realm ActualRunAdmissionScales
open WilsonVacuumPreResetFiniteHeatCourse
open scoped Classical BigOperators

open WilsonVacuumPreResetDatedCourse (coin)
open FVA1Physical.TwoReset (massJets)
open AllOrder.Floe

open FVA1Physical.TwoReset (Prescription AffineMass)
open AllOrder.Floe.Step.PlanV

open PhysicalNext PhysicalNext.Repeat Legato WilsonLimitConstruction Next.Foundations
open WilsonSubmittedPeriodSeam (price weight Bill)

def Paid (N j p e t d:ℕ)(π:ℕ→Layout G)(Γ:ℕ→Pace.Coin)(live:j<N):Prop:=
  ∀(F:Forest (step R j p).ratio)(tag:(step R j p).Choices)
    {T:Type}[DecidableEq T][Fintype T]{J:Census T}(Q:Bulk.Colors J G (fine R j p))
    (x y:Stationary.Link G (coarse R j p)),
    let current:=QuadraticLocal.Fk.grant (π (j+1)) (Step.tape (e+2)) Q
    let program:=(RunFormalChain.fromRun R).step N j p live
    let field:=fun z:Stationary.Link G (coarse R j p)=>Stationary.arm G _ 1 z
    let lower:=Pace.grouping (Γ j) (π j) (Step.tape (e+2))
      (R.family.path.levels.params j).clip (R.alloy.B.kin.path N j) t (coarse R j p)
    ‖(Symmetry.Orbit.ground program F tag current (e+2) t (field x)
      -Symmetry.Orbit.ground program F tag current (e+2) t (field y))
      +((lower (flatten (field x))-lower (flatten (field y)):ℝ):ℂ)‖≤price R t d j p*weight R t j p x y

theorem original (G:Gauge):
    ∃(P:FundedCompanySelection.Prediction G)(cost:ℕ→ℕ),
      FundedPredictionSupply.AllPrices (@P) ∧
      ∀(C:Run G),G.Simple→RG05Preconstruction.ReadoutPurchase C.b→P C.kit→
      ∀e:ℕ,∀ᶠm:ℕ in atTop,∀N,m ≤ N →
      ∀(D:Roots (G:=G) C.metals.p.profile C.metals.K C.metals.p.kernel)(Q:D.Tab C.rolls)
        (π:ℕ→Layout G)(Γ:ℕ→Pace.Coin),Step.PlanV.Path D C.alloy Q e N m π Γ→
        Step.PlanV.Spec D Q C.alloy C.kit→
        ∀j,m ≤ j → ∀live:j<N,∀p t,t ≤ e+2 → Paid C N j p e t (cost t) π Γ live:=by
  obtain ⟨fees,cost,elected⟩:=WilsonSubmittedCalendar.original G
  let P:=@FundedPredictionSupply.Both G (@FundedMarkedCoverRows.prices G fees) (@FundedOriginalVacuumPaths.prices G)
  refine ⟨@P,cost,(fun S c=>FundedPredictionSupply.both
    (FundedMarkedCoverRows.purchase fees S c) (FundedOriginalVacuumPaths.buy S c)),?_⟩
  intro C simple reading buy e
  obtain ⟨W,course⟩:=WilsonPositionProgramFullReceivingMass.original C simple fees buy.1 buy.2 e
  have simultaneous:∀ᶠj:ℕ in atTop,∀t:Fin (e+3),Bill C t (cost t) j:=
    Filter.eventually_all.2 (fun t=>elected C simple reading buy.1 t)
  obtain ⟨j₀,sheets⟩:=Filter.eventually_atTop.1 simultaneous
  filter_upwards [course,eventually_ge_atTop j₀] with m enter mh
  intro N hm D Q π Γ route audit j lower live p t rank
  obtain ⟨Z,issued,_,hearing⟩:=enter N hm
  obtain ⟨aligned,regraded⟩:=hearing D Q π Γ route audit
  obtain ⟨σ,_,_,upper⟩:=issued (j+1) (by omega) (by omega)
  obtain ⟨s,_,_,bottom⟩:=issued j lower live.le
  intro F tag T _ _ J color x y
  have bill:=sheets j (mh.trans lower) ⟨t,by omega⟩ N m p e Z π Γ aligned lower live
    F tag color σ _ s _ upper bottom rank x y
  simpa only [regraded j lower live t rank (coarse C j p)] using bill

end YM.Integration.WilsonPositionProgramOriginalQuietTrajectory
end
