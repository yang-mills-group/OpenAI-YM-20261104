import YM.Integration.WilsonReceivedDepositedSocketRows
import YM.Integration.WilsonNeutralTwoPrintPathInheritedBlocks
import YM.Integration.WilsonReceivedCanonicalSocketLevels
import YM.Integration.WilsonReceivedCanonicalSocketMist

/-! A fixed list of genuine, separately located previous words enters one measured
finite Gaussian. No child or centre is summed in this comparison. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedDepositedOrbitalFixedMoments
open Function Filter Finset Lattice Wilson Laurent RG Source Labels Marker Multi QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Sunrise
open Comparison.RG02 Comparison.RG02.Cumulants Next.SectorChange AllOrder AllOrder.Floe
open PhysicalNext.Repeat.Legato Further.PhysicalPeriodLimitF933 Macrame Shingle
open FVA1Physical.TwoReset WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Embroider WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Soil
open WilsonVacuumPreResetStationaryChange WilsonVacuumPreResetDepositedGeometric
open WilsonOriginalStarSceneWords WilsonThermometerDeclaredSeeds WilsonOriginalThermometerPalette
open WilsonReceivedCanonicalSocketRows WilsonReceivedCanonicalSocketFields WilsonReceivedCanonicalSocketSeed
open Pressure Push Push.AbsoluteSums Precision Tree Exterior Bloch PowerSeries
open PhysicalForestMarkedRay FVA1Physical.TwoReset
open scoped ContDiff Topology Classical BigOperators Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
open WilsonLimitConstruction Work.F08 FullQLocal FullQLocal.RenderedStep
open WilsonVacuumPreResetDepositedIntegrand WilsonOriginalOccupiedForestIntegral WilsonOriginalMeasuredOccupiedForest
open WilsonVacuumPreResetOriginalOutput (covered)
open WilsonOriginalRelativeFoldedQuiet (relative)
open WilsonOriginalEarnedUnaryDriver (driver)
open WilsonVacuumPreResetDatedDeposit (Issued)
open WilsonOriginalThreePurchasedRays (prescribed)

open LocalComparison Comparison.RG02.Cumulants Comparison.RG02.Assembly Order AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open PertExtension Series WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank
open WilsonReceivedCanonicalSocketChannels
open WilsonOriginalEarnedUnaryDriver (driver)
open WilsonCoeffUV.Winding WilsonCoeffUV.Power Next.Rank
open FreeResolvent
open WilsonOriginalChargedForestQ WilsonVacuumPreResetFiniteRegister
open WilsonCapturedPrimaryWindingVerseRoster (coefficient)
open WilsonOriginalFoldedMarkedRightColumn WilsonCoeffUV.Mer
open WilsonCoeffUV.Wheel.Mark

open WilsonReceivedCanonicalSocketSeed
open WilsonNeutralTwoPrintPathInheritedBlocks (gathered)
open WilsonReceivedCompactVerseEntrance (CoverBill submit)
open WilsonReceivedDepositedOrbitalPages (offered)
open WilsonCoeffUV.Embroider.Canvas WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Bank.Mosaic.Near
variable {G:Gauge}{n:ℕ}{D k:Fin n→ℕ}{I:Type}[Fintype I][DecidableEq I]
  (old:Outerm G D)(q:ℕ)(J:I→Finset (Fin n))(c:I→Fin n)(site:I→Fin n→Lattice.Cover)(A:I→Case D)

def point:Vote 1:=claim 1 (contact 1) zeroC
def reading {I:Type}:Case (fun _:I=>1):=fun _=>page 1 (sheet 1)

omit [Fintype I] [DecidableEq I] in
theorem charge (i:I):point (reading i)=1:=by
  change iteratedFDeriv ℝ 0 (fun _:E=>(1:ℝ)) (zeroC:E) (dot ∘ (Fin.elim0:Fin 0→Axis))=1
  rw [iteratedFDeriv_zero_apply]

def program:Outerm G (fun _:I=>1):=
  gathered old k q J c site (fun i=>(touch (A i) (J i)).smulRight point)

variable (well:Wellness k old){σ cash:ℝ}(hs:0<σ)(fund:1≤cash)(bill:CoverBill old q σ cash)
  (live:∀i,c i∈J i)

include well hs fund bill live in
theorem authentic:
    Wellness (fun i=>mass k (J i)) (program (k:=k) old q J c site A) ∧
    CoverBill (program (k:=k) old q J c site A) q σ
      (WilsonNeutralTwoPrintPathInheritedBlocks.amount cash J (fun i=>(touch (A i) (J i)).smulRight point)):=by
  exact (WilsonNeutralTwoPrintPathInheritedBlocks.original old well hs fund bill J c live site
    (fun i=>(touch (A i) (J i)).smulRight point)).2

local notation "M" z:max => program (k:=k) old q J c site A z
local notation "degree" => fun u=>mass k (J u)
variable (R:Run G)(N i per:ℕ)(hi:i<N)(F:Forest (step R i per).ratio)
  (tag:(step R i per).Choices)(z:I→Lattice.Cover)
local notation "S" => step R i per
local notation "f" => fine R i per
local notation "H" => WilsonVacuumPreResetStationaryChange.model R N i per hi
local notation "vac" => relative R N i per hi F (covered R N i per)
local notation "real" u:max => offered old k q (site u) (A u) (J u) (c u) (f) (wrap (f) (z u))
local notation "inlet" u:max => WilsonOriginalFoldedMarkedRightColumn.before R N i per hi F (real u)

theorem socket (u:I):pPly reading {u} ((((M z) {u}).1) (f))=real u:=by
  have own:=WilsonNeutralTwoPrintPathInheritedBlocks.reading old k q J c site A (fun _=>point) u z reading (f)
  simpa only [program,charge,one_smul] using own

include well hs fund bill live in
theorem ordinary (s:Finset I):
    WilsonOriginalFoldedMarkedRightColumn.before R N i per hi F
      ((WilsonReceivedDepositedVerseCensus.ordinary (M z) reading s).1 (f))=∏u∈s,inlet u:=by
  let pay:Eu (degree) (M z):=(authentic old q J c site A well hs fund bill live).1.level' z
  have dark (t:Finset I)(away:∀a:I,t≠{a}):(M z) t=0:=
    WilsonNeutralTwoPrintPathRebadge.dark _ z t away
  let L:=SignedMeasuredSourceSeries.probe (S) F (saddle R N i per F) (fderiv ℝ ((H).b F) 0)
  change L (readO reading (levelsO (M z) s) (f))=_
  rw [WilsonReceivedCanonicalSocketLevels.original (M z) pay dark reading (f) s,map_prod]
  apply Finset.prod_congr rfl
  intro u _
  exact congrArg (fun T=>L (flash T)) (socket old q J c site A R i per z u)

include well hs fund bill live in
theorem original (simple:G.Simple)(s:Finset I):
    Wick (Woods G (coarse R i per)) ((H).covariance F tag) (raiseE (vac)*∏u∈s,inlet u)=
      Wick (Woods G (coarse R i per)) ((H).covariance F tag) (raiseE (vac))*
        flash (WilsonOriginalFoldedMarkedRightColumn.filed R N i per F (mass (degree) s)
          ((WilsonReceivedDepositedVerseCensus.ordinary (M z) reading s).1 (f))):=by
  rw [←ordinary old q J c site A well hs fund bill live R N i per hi F z s]
  have paid:Eu (degree) (M z):=(authentic old q J c site A well hs fund bill live).1.level' z
  have row:Auth (mass (degree) s) (WilsonReceivedDepositedVerseCensus.ordinary (M z) reading s):=
    (placedO (M z) paid s).tuft (touch reading s)
  exact WilsonOriginalFoldedMarkedRightColumn.normalized R N i per hi F tag simple _ _
    (row.span (f)) (row.pale (f))

end YM.Integration.WilsonReceivedDepositedOrbitalFixedMoments
end
