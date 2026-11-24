import YM.Integration.WilsonReceivedDepositedOrbitalThermals
import YM.Integration.WilsonReceivedDepositedOrbitalMonomials
import YM.Integration.WilsonOriginalCensusWickPages

/-! On the genuine copied Wilson field introduce one temporary mark at each available
sheet of each previously deposited connected word. Its root is the original sheet
and its complete thermal polynomial includes its signed marked scalar. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedDepositedOrbitalPhases
open Function Filter Finset Lattice Laurent RG Wilson Stationary Primitives.TwoWave
open QuadraticLocal QuadraticLocal.Poetry QuadraticLocal.Sunrise QuadraticLocal.Earn QuadraticLocal.Sunrise.Aviary QuadraticLocal.Affinity
open Marker Next.SectorChange Multi Comparison.RG02 AllOrder AllOrder.Floe
open Further.PhysicalPeriodLimitF933 Macrame Shingle Precision Tree Exterior PhysicalNext.Repeat.Legato
open AllOrder.Ker AllOrder.Ker.Start AllOrder.Haiku AllOrder.Ink WilsonCoeffUV WilsonCoeffUV.Blue PowerSeries
open WilsonOlderFreshGraphVote WilsonNeutralRenderedColumn WilsonOlderFreshGraphArmada FVA1Physical.TwoReset
open WilsonVacuumPreResetStationaryChange WilsonOriginalPrimerReplicatedInk PhysicalForestMarkedRay PhysicalForestRay
open FreeResolvent WilsonVacuumPreResetDepositedGeometric WilsonVacuumPreResetDepositedLetters WilsonVacuumPreResetFiniteRegister
open WilsonOriginalPointCompactRoster WilsonOriginalThreeCopiedCharts
open scoped Classical BigOperators ContDiff Topology
open LocalComparison Comparison.RG02.Cumulants Comparison.RG02.Assembly Order AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open PertExtension Series WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank
open WilsonLimitConstruction Work.F08 FullQLocal FullQLocal.RenderedStep
open WilsonVacuumPreResetDepositedIntegrand WilsonOriginalOccupiedForestIntegral WilsonOriginalMeasuredOccupiedForest
open WilsonVacuumPreResetOriginalOutput (covered)
open WilsonOriginalRelativeFoldedQuiet (relative)
open WilsonOriginalEarnedUnaryDriver (driver)
open WilsonOriginalThreePurchasedRays (prescribed)
attribute [local instance] Gauge.frobInner
open WilsonOriginalMixedBlockRows WilsonRegisteredPairUnaryWallet WilsonOriginalCensusCopySlate
open WilsonOlderFreshGraphSlate (Copy)
variable {G:Gauge} {n:Side} {V I:Type} [Fintype V] [DecidableEq V] [Fintype I]
  {P:Passport n V}(binders:I→Binder P (Stock.census V))(grades:V→ℕ)
  (R:Run G)(N i per:ℕ)(hi:i<N)(F:Forest (step R i per).ratio)(tag:(step R i per).Choices)
  (h:n.val∣(fine R i per).val)(x:Wallet (room V))
  (Z:I→(n:Side)→Site n→PChart G n)(B:fieldDir G (coarse R i per) 1)(z:Precision.Key F G→ℝ)
local notation "J" => Stock.census V
open Function Finset Lattice Wilson WilsonCoeffUV WilsonCoeffUV.Blue
open WilsonCoeffUV.Blue.Cameo Marker QuadraticLocal QuadraticLocal.Earn FVA1Physical.TwoReset PowerSeries
open scoped Classical BigOperators


open WilsonOriginalCensusPaidForest (ray)
open WilsonOriginalFoldedMarkedRightColumn (before)
open WilsonOriginalCensusPageRays (atLift)
open WilsonOriginalGaussianPaidTable (presented)
open MeasureTheory YM.Comparison.RG02.Cumulants

local notation "finePage" => Fin (Pages n (fine R i per))
local notation "whereFrom" => Option (I × finePage)
local notation "full" => WilsonOriginalCensusPaidForest.value binders R N i per hi F h x Z B z


open WilsonReceivedDepositedOrbitalSlice WilsonReceivedDepositedOrbitalMonomials

def name (u:I×finePage):Hot (J):=⟨(binders u.1).mode,⟨(binders u.1).front,(binders u.1).east⟩⟩

def temporary (r:ℕ):Grade (Stock.census (I×finePage)) r:=
  source (Stock.census (I×finePage)) (Stock.census (I×finePage)).fire
    (Join.projectRight _ _ (lit (Board (J) r) (full r)))
    (fun u=>Poly.inject fun t=>(t.val.card.factorial:ℂ)*atLift binders R N i per hi F h x Z B z u.1 u.2 t.val.card)

theorem original (shell:∀l a,shellK (∑v∈(binders l).mode.val,grades v) (Z l (fine R i per) a))
    (pure:∀l a j,Pure (Z l (fine R i per) a j))(r:ℕ):
    hom (WilsonReceivedDepositedAlias.fold (J) (name binders R i per))
      r (temporary binders R N i per hi F h x Z B z r)=lit (Board (J) r) (full r):=by
  classical
  rw [temporary,relabel]
  apply Join.both_parts
  intro s t
  rw [WilsonReceivedDepositedOrbitalMonomials.coefficient]
  by_cases used:s.val.Nonempty
  · rw [if_neg ((hot_iff_ne s).mp used),zero_add]
    have whole:(Join.pair s t).val.Nonempty:=by
      obtain ⟨v,hv⟩:=used
      exact ⟨Sum.inl v,by simpa [Join.pair] using hv⟩
    let l:Hot (Board (J) r):=⟨Join.pair s t,whole⟩
    rw [show (lit (Board (J) r) (full r)).part (Join.pair s t)=full r l from part_lit _ l]
    rw [WilsonOriginalCensusWickPages.bill binders grades R N i per hi F h x Z B z shell pure l]
    simp only [Fintype.sum_option,WilsonOriginalCensusWickPages.entry,l,Join.left_pair,Join.right_pair,used,
      if_true,zero_add,true_and]
    refine Finset.sum_congr rfl fun u _=>?_
    by_cases eqn:s=(binders u.1).mode
    · simp only [name,eqn,if_true]
      rfl
    · simp only [name,eqn,Ne.symm eqn,if_false]
  · have empty:s=(J).quiet:=not_not.mp (fun h=>used ((hot_iff_ne s).mpr h))
    subst s
    rw [if_pos rfl,Join.right_projection]
    have none(u:I×finePage):(J).quiet ≠ (name binders R i per u).val:=
      Ne.symm ((hot_iff_ne _).mp (name binders R i per u).property)
    simp only [none,if_false,Finset.sum_const_zero,add_zero]

end YM.Integration.WilsonReceivedDepositedOrbitalPhases
end
