import YM.Integration.WilsonReceivedDepositedOrbitalFixedMoments
import YM.Integration.WilsonReceivedDepositedOrbitalWick

/-! The independent comparison for a selected finite set of deposited sheets uses
only that set, with all its proper faces and its true lifted fine locations. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedDepositedOrbitalRetained
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

open WilsonOriginalThreeCopiedCharts WilsonOriginalMixedBlockRows WilsonOlderFreshGraphSlate
open WilsonOriginalCensusCopySlate WilsonReceivedDepositedOrbitalFixedMoments
open WilsonVacuumPreResetDepositedLetters WilsonCoeffUV.Bank.Mosaic
variable {G:Gauge}{n:ℕ}{n':Side}{I:Type}
  {P:Passport n' (Fin n)}(B:I→Binder P (Stock.census (Fin n))){D k:Fin n→ℕ}
  (old:Outerm G D)(q:ℕ)(root:I→Fin n)(y:Fin n→Lattice.Cover)(t:Case D)
  (R:Run G)(N i per:ℕ)(hi:i<N)(F:Forest (step R i per).ratio)(tag:(step R i per).Choices)
  (h:n'.val∣(fine R i per).val)
local notation "ff" => fine R i per
local notation "load" => I×Fin (Pages n' (ff))
local notation "K₀" => model R N i per hi
local notation "vac" => relative R N i per hi F (covered R N i per)
local notation "held" u:max => (page h (B (u).1).center (u).2).val
local notation "field" u:max => offered old k q y t (B (u).1).mode.val (root (u).1) (ff) (held u)
local notation "before" u:max => WilsonOriginalFoldedMarkedRightColumn.before R N i per hi F (field u)
variable (T:Finset (I×Fin (Pages n' (fine R i per))))
local notation "mode" => fun u:T=>(B u.val.1).mode.val
local notation "section" => fun u:T=>root u.val.1
local notation "degree" => fun u:T=>mass k ((B u.val.1).mode.val)

def family:Outerm G (fun _:T=>1):=
  program (k:=k) old q (mode) (section) (fun _:T=>y) (fun _:T=>t)

def roots (u:T):Lattice.Cover:=Lattice.lift (held u.val)

local notation "X" => family (k:=k) B old q root y t R i per T
local notation "placed" => roots B R i per h T
local notation "M" => (X) (placed)
local notation "read" => @reading T

def income (s:Finset T):Ink (Woods G (coarse R i per)):=
  flash (WilsonOriginalFoldedMarkedRightColumn.filed R N i per F (mass (degree) s)
    ((WilsonReceivedDepositedVerseCensus.ordinary (M) (read) s).1 (ff)))

variable (well:Wellness k old){σ cash:ℝ}(hs:0<σ)(fund:1≤cash)(book:CoverBill old q σ cash)
  (inside:∀u,root u∈(B u).mode.val)

include well hs fund book inside in
theorem paid:
    Wellness (degree) (X) ∧ CoverBill (X) q σ (WilsonNeutralTwoPrintPathInheritedBlocks.amount cash (mode)
      (fun u=>(touch t ((B u.val.1).mode.val)).smulRight point)):=by
  exact authentic old q (mode) (section) (fun _:T=>y) (fun _:T=>t) well hs fund book (fun u=>inside u.val.1)

include well hs fund book inside in
theorem ordinary (simple:G.Simple)(s:Finset T):
    Wick (Woods G (coarse R i per)) ((K₀).covariance F tag)
      (raiseE (vac)*∏u∈s,(before u.val))=
      Wick (Woods G (coarse R i per)) ((K₀).covariance F tag) (raiseE (vac))*
        income (k:=k) B old q root y t R N i per F h T s:=by
  have hit:=WilsonReceivedDepositedOrbitalFixedMoments.original old q (mode) (section) (fun _:T=>y) (fun _:T=>t)
    well hs fund book (fun u=>inside u.val.1) R N i per hi F tag (placed) simple s
  simpa only [family,roots,wrap_lift,income] using hit

include well hs fund book inside in
theorem whole (simple:G.Simple):
    Wick (Woods G (coarse R i per)) ((K₀).covariance F tag) (raiseE (vac)*∏u∈T,(before u))=
      Wick (Woods G (coarse R i per)) ((K₀).covariance F tag) (raiseE (vac))*
        income (k:=k) B old q root y t R N i per F h T univ:=by
  rw [←Finset.prod_coe_sort T (fun a=>(before a))]
  exact ordinary B old q root y t R N i per hi F tag h T well hs fund book inside simple univ

include well hs fund book inside hi in
/-- The registered kinetic substitution occurs once on every ordinary face. -/
theorem reset (simple:G.Simple):
    let γ:=ratioHigh (levels R) R.metals.O N i
    Equation (fun s=>redo (U:=Woods G (coarse R i per)) γ (income (k:=k) B old q root y t R N i per F h T s))
      (fun s=>flash (pPly (read) s (mist (step R i per) F (upper R N i) (prediction R N i per)
        (ratio R) (covered R N i per) (M) γ (degree) s))):=by
  exact WilsonReceivedCanonicalSocketMist.deposited R N i per hi F (M)
    ((paid B old q root y t R i per T well hs fund book inside).1.level' (placed)) (read) simple

end YM.Integration.WilsonReceivedDepositedOrbitalRetained
end
