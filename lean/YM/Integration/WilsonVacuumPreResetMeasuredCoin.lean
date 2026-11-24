import YM.Integration.WilsonVacuumPreResetDatedBirth
import YM.Integration.WilsonConditionalTaylorForestHaar

/-! One deposited cover prescription and the actual kinetic coin on every measured PlanV path. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetMeasuredCoin
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
open FVA1Physical.TwoReset (AffineMass)
open PertExtension.Series PowerSeries
open AllOrder AllOrder.Floe

open AllOrder.Floe.Step.PlanV FVA1Physical.TwoReset
open WilsonVacuumPreResetDatedCourse (coin)
open Primitives.TwoWave.RealSlice

structure Agrees (N m e:ℕ)(Z:ℕ→SeriesA G)(π:ℕ→Layout G)(Γ:ℕ→Pace.Coin):Prop where
  jets:∀ i,m ≤ i→i≤N→∀l≤e+2,massJets R N i e (π i) l=massJets R N i e (bank (Z i)) l
  rates:∀ i,m ≤ i→i<N→∀l≤e+2,Γ i l=coin R N i l
  marked:∀i,m ≤ i→∀h:i<N,∀p (F:Forest ((levels R).clock.op i p).ratio)
    (tag:((levels R).clock.op i p).Choices) {V:Type} [Fintype V] [DecidableEq V] {J:Census V}
    (Y:Bulk.Colors J G (R.family.side (i+1) p))(x:Stationary.Link G (R.family.side i p)) (l:ℕ),l≤e+2→
    Bulk.Fk ((RunFormalChain.fromRun R).step N i p h) F tag
      (QuadraticLocal.Fk.grant (π (i+1)) (Step.tape (e+2)) Y) (Stationary.arm G _ 1 x) l=
    Bulk.Fk ((RunFormalChain.fromRun R).step N i p h) F tag
      (QuadraticLocal.Fk.grant (bank (Z (i+1))) (Step.tape (e+2)) Y) (Stationary.arm G _ 1 x) l

theorem compared (simple:G.Simple){N m e:ℕ}{Z:ℕ→SeriesA G} (P:Prescription R (fun i=>bank (Z i)) (coin R N) N m e)
    (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)(Q:D.Tab R.rolls)
    (π:ℕ→Layout G)(Γ:ℕ→Pace.Coin)(path:Step.PlanV.Path D R.alloy Q e N m π Γ)
    (audit:Step.PlanV.Spec D Q R.alloy R.kit)
    (large:∀i,m ≤ i→i<N→Bid.Larger (G:=G) ((levels R).clock.op i 0)):Agrees R N m e Z π Γ:=by
  let X:=fun i=>bank (Z i)
  have native:=FVA1Physical.TwoReset.authentic R π Γ D Q path audit large
  have jet:=FVA1Physical.TwoReset.every_jet R π X Γ (coin R N) D Q path native P simple
  refine ⟨jet,fun i lo hi l hl=>FVA1Physical.TwoReset.every_unit R π X Γ (coin R N) D Q path native P simple lo hi l hl,?_⟩
  intro i lo hi p F tag V _ _ J Y x l hl
  exact FVA1Physical.TwoReset.official_call R hi (native.legal (i+1) (by omega) hi)
    (P.legal (i+1) (by omega) hi) (jet (i+1) (by omega) hi) F tag Y x hl

theorem original (simple:G.Simple)(v:ℕ→Gear G→ℝ)(rows:FundedMarkedCoverRows.prices v R.kit)
    (paths:FundedOriginalVacuumPaths.prices R.kit)(e:ℕ):
    ∃W:Credit,∀ᶠ m:ℕ in atTop,∀N:ℕ,m≤N→∃Z:ℕ→SeriesA G,
      (∀j,m≤j→j≤N→∃σ:ℝ,0<σ ∧ σ⁻¹≤zz (levels R) j ∧
        Issued R N j e (Z j) σ (W.buy (zz (levels R) j)+zz (levels R) j*(levels R).clock.loopCap j)) ∧
      Prescription R (fun i=>bank (Z i)) (coin R N) N m e ∧
      ∀(D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)(Q:D.Tab R.rolls)
        (π:ℕ→Layout G)(Γ:ℕ→Pace.Coin),Step.PlanV.Path D R.alloy Q e N m π Γ→
        Step.PlanV.Spec D Q R.alloy R.kit→Agrees R N m e Z π Γ:=by
  obtain ⟨W,dates⟩:=WilsonVacuumPreResetDatedCourse.original R simple v rows paths e
  refine ⟨W,?_⟩
  filter_upwards [dates,WilsonConditionalTaylorForestHaar.ready R.family.path] with m choose large
  intro N top
  obtain ⟨Z,receipt,law,every⟩:=choose N
  obtain ⟨σ,_,_,birth⟩:=receipt N top (le_refl _)
  have policy:Prescription R (fun i=>bank (Z i)) (coin R N) N m e:=
    ⟨law,fun _ hl=>WilsonVacuumPreResetDatedBirth.original R birth hl,every⟩
  exact ⟨Z,receipt,policy,fun D Q π Γ path audit=>compared R simple policy D Q π Γ path audit
    (fun i lo _=>large i lo 0)⟩

end YM.Integration.WilsonVacuumPreResetMeasuredCoin
