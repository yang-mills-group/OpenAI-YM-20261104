import YM.Integration.WilsonOriginalCensusWickPages
import YM.Integration.WilsonOriginalGaussianPaidTable
import YM.Integration.WilsonOriginalThreeGaussianReturn

/-! The finite Gaussian driver on the deposited branch roster. Each original mode uses
its whole copied word at its own deposited site and at its actual source degree. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusPolyPages
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
  {q:ℕ}{σ:ℝ}(T:∀l,Copy G (∑v∈(binders l).mode.val,grades v) q σ)
  (R:Run G)(N i per:ℕ)(hi:i<N)(F:Forest (step R i per).ratio)(tag:(step R i per).Choices)
  (h:n.val∣(fine R i per).val)(x:Wallet (room V))(L:Layout G)(tape:Finset Age)
  (Z:I→(n:Side)→Site n→PChart G n)(B:fieldDir G (coarse R i per) 1)(z:Precision.Key F G→ℝ)
local notation "own" l:max => (T (l)).rows (WilsonOlderFreshGraphPointWallet.point (binders (l)).center) disk
local notation "M" => mounted binders (fun l=>own l)
local notation "J" => Stock.census V
local notation "joint" => copyColor h M grades (fun a=>(M a).paint x) L tape
local notation "S" => step R i per
local notation "saddle₀" => saddle R N i per F
local notation "K₀" => model R N i per hi

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

open WilsonOriginalFoldedMarkedRightColumn (before)
open SignedRegisteredMarkedProgram (register)
open WilsonOriginalCensusWickPages (entry)

def single {r:ℕ}(s:Hot (Board J r))(u:whereFrom):Next.Rank.Normal.poly (Precision.Key F G):=
  let j:=(Join.right s.val).val.card
  match u with
  | none=>if (Join.left s.val).val.Nonempty then 0 else
      MvPolynomial.C (j.factorial:ℂ)*register F B
        (coeff j (WilsonOriginalRelativeFoldedQuiet.relative R N i per hi F (WilsonVacuumPreResetOriginalOutput.covered R N i per)))
  | some (l,p)=>if (Join.left s.val).val.Nonempty ∧ (binders l).mode=Join.left s.val then
      MvPolynomial.C ((j.factorial:ℂ)*(∏v∈(binders l).mode.val,(x v).val))*
        register F B (coeff j (before R N i per hi F (Z l (fine R i per) (page h (binders l).center p).val))) else 0

omit [Fintype V] [DecidableEq V] [Fintype I] in
private theorem ink (k:ℂ)(T:MvPolynomial (Active G F⊕Woods G (coarse R i per)) ℝ):
    Cloud.paint z (MvPolynomial.C k*register F B T)=k*Complex.ofReal (MvPolynomial.eval (Sum.elim z (flatten B)) T):=by
  rw [map_mul,SignedRegisteredMarkedProgram.reading,WilsonOriginalChargedForestQ.same_axes R i per F B z]
  simp [Cloud.paint,PhysicalForestRay.sample]
theorem read {r:ℕ}(s:Hot (Board J r))(u:whereFrom):
    Cloud.paint z (single binders R N i per hi F h x Z B s u)=entry binders R N i per hi F h x Z B z s u:=by
  classical
  cases u with
  | none=>
    by_cases live:(Join.left s.val).val.Nonempty
    · simp [single,WilsonOriginalCensusWickPages.entry,live]
    · simp [single,WilsonOriginalCensusWickPages.entry,live,WilsonOriginalCensusPaidForest.value,Cloud.paint]
  | some lp=>
    obtain ⟨l,p⟩:=lp
    by_cases live:(Join.left s.val).val.Nonempty ∧ (binders l).mode=Join.left s.val
    · simp only [single,WilsonOriginalCensusWickPages.entry,live,WilsonOriginalCensusPageRays.atLift]
      exact (ink R i per F B z _ _).trans (mul_assoc ..)
    · simp [single,WilsonOriginalCensusWickPages.entry,live]

end YM.Integration.WilsonOriginalCensusPolyPages
end
