import YM.Integration.WilsonOriginalOccupiedForestIntegral
import YM.Integration.WilsonVacuumPreResetMeasuredCoin

/-! The original numerical course reads its funded joint numerator on the independently issued quiet bank. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalMeasuredOccupiedForest
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


open WilsonVacuumPreResetMeasuredCoin (Agrees)
open WilsonOriginalOccupiedForestIntegral (numerator)
open Next.SectorChange MeasureTheory

structure Read (N m e:ℕ)(Z:ℕ→SeriesA G)(π:ℕ→Layout G)(Γ:ℕ→Pace.Coin):Prop where
  course:Agrees R N m e Z π Γ
  filed : ∀ (i : ℕ), m ≤ i → ∀ (h : i < N) (p : ℕ) (F:Forest ((levels R).clock.op i p).ratio)
    (tag:((levels R).clock.op i p).Choices) {V:Type} [Fintype V] [DecidableEq V] {J:Census V}
    (Y:Bulk.Colors J G (R.family.side (i+1) p)), Bulk.Well Y →
    ∀(x:Stationary.Link G (R.family.side i p)) (l:ℕ), l ≤ e+2 → ∀ s : (Order.Board J l).Mode,
    (Bulk.Fk ((RunFormalChain.fromRun R).step N i p h) F tag
      (QuadraticLocal.Fk.grant (π (i+1)) (Step.tape (e+2)) Y) (Stationary.arm G _ 1 x) l).part s =
      ∫ z,(WilsonOriginalOccupiedForestIntegral.numerator R N i p h F (Z (i+1)) Y
        (Stationary.arm G _ 1 x) l z).part s ∂Next.SectorChange.Gaussian.cloud
          (((RunFormalChain.fromRun R).step N i p h).covariance F tag)

theorem original (simple:G.Simple)(v:ℕ→Gear G→ℝ)(rows:FundedMarkedCoverRows.prices v R.kit)
    (paths:FundedOriginalVacuumPaths.prices R.kit)(e:ℕ):
    ∃W:Credit,∀ᶠ m:ℕ in atTop,∀N:ℕ,m≤N→∃Z:ℕ→SeriesA G,
      (∀j,m≤j→j≤N→∃σ:ℝ,0<σ ∧ σ⁻¹≤zz (levels R) j ∧
        Issued R N j e (Z j) σ (W.buy (zz (levels R) j)+zz (levels R) j*(levels R).clock.loopCap j)) ∧
      Prescription R (fun i=>bank (Z i)) (coin R N) N m e ∧
      ∀(D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)(Q:D.Tab R.rolls)
        (π:ℕ→Layout G)(Γ:ℕ→Pace.Coin),Step.PlanV.Path D R.alloy Q e N m π Γ→
        Step.PlanV.Spec D Q R.alloy R.kit→Read R N m e Z π Γ:=by
  obtain ⟨W,dates⟩:=WilsonVacuumPreResetMeasuredCoin.original R simple v rows paths e
  refine ⟨W,?_⟩
  filter_upwards [dates] with m choose
  intro N cut
  obtain ⟨Z,issued,policy,on_course⟩:=choose N cut
  refine ⟨Z,issued,policy,?_⟩
  intro D Q π Γ path spec
  have A:=on_course D Q π Γ path spec
  refine ⟨A,?_⟩
  intro i low h p F tag V _ _ J Y good x l hl s
  obtain ⟨σ,_,_,bank⟩:=issued (i+1) (by omega) h
  rw [A.marked i low h p F tag Y x l hl]
  exact WilsonOriginalOccupiedForestIntegral.integrated R N i p h F tag (Z (i+1)) Y
    ((levels R).budget (i+1)) (e+2) bank.positive bank.purchase bank.lower
    (fun a ha=>by have z:=bank.upper a ha; omega) _ l good s

end YM.Integration.WilsonOriginalMeasuredOccupiedForest
