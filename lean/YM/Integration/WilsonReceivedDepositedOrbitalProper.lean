import YM.Integration.WilsonReceivedDepositedOrbitalResponse
import YM.Integration.WilsonReceivedDepositedOrbitalMode

/-! A picked block of sheets has a single independently filed family for all its
proper modes. Restricting to a proper subfamily and then reading has exactly the same
ordinary numerator before the same one vacuum division. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedDepositedOrbitalProper
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
variable {G:Gauge}{n:ℕ}{n':Side}{I:Type}[Fintype I]
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

open WilsonCapturedPrimaryWindingVerseRoster (coefficient)
open WilsonOriginalMixedGaussianTable (stock)
open WilsonReceivedDepositedOrbitalConditioned (staged)
open WilsonReceivedDepositedOrbitalRetained (income)
open private flat_constant from YM.Integration.WilsonReceivedCanonicalSocketWick
open private opening from YM.Integration.WilsonVacuumPreResetDepositedAction
variable (well:Wellness k old){σ cash:ℝ}(hs:0<σ)(fund:1≤cash)(book:CoverBill old q σ cash)
  (inside:∀u,root u∈(B u).mode.val)
local notation "Z₁" => I×Fin (Pages n' (ff))
local notation "J₁" => Stock.census (Z₁)
local notation "Q₁" => (K₀).covariance F tag
local notation "bank" => fun l:I=>offered old k q y t (B l).mode.val (root l)
local notation "mask" => fun l:I=>(B l).mode.val
local notation "massAt" => fun l:I=>mass k ((B l).mode.val)
local notation "picked" a:max => income (k:=k) B old q root y t R N i per F h a univ
variable (x:Affinity.Wallet (WilsonOriginalMixedBlockRows.room (Fin n)))
  (a:fieldDir G (coarse R i per) 1)
local notation "c₁" => fun u:(Z₁)=> ∏v∈(B u.1).mode.val,(x v).val
local notation "piece" => fun u:(Z₁)=>coefficient (J₁) (J₁).fire (c₁) u
local notation "amount" => fun s:Finset (Z₁)=>∏u∈s,(piece) u
local notation "V₀" => Wick (Woods G (coarse R i per)) (Q₁) (raiseE (vac))


open WilsonReceivedDepositedOrbitalMode (face)
variable (T:Finset (I×Fin (Pages n' (fine R i per))))

def retain (s:Finset T):Finset (I×Fin (Pages n' (ff))):=
  s.map (Function.Embedding.subtype _)

include well hs fund book inside hi tag in
omit [Fintype I] in
theorem same (simple:G.Simple)(s:Finset T):
    income (k:=k) B old q root y t R N i per F h T s=
      (picked (retain R i per T s)):=by
  let W₀:=Wick (Woods G (coarse R i per)) (Q₁) (raiseE (vac))
  have top:constantCoeff W₀=1:=opening _ _ (flat_constant R N i per hi F)
  have nz:W₀≠0:=by
    intro zero
    rw [zero,map_zero] at top
    exact zero_ne_one top
  apply mul_left_cancel₀ nz
  have lower:=WilsonReceivedDepositedOrbitalRetained.ordinary B old q root y t R N i per hi F tag h T well hs fund book inside simple s
  have small:=WilsonReceivedDepositedOrbitalRetained.whole B old q root y t R N i per hi F tag h (retain R i per T s)
    well hs fund book inside simple
  rw [←lower,←small]
  rw [retain,Finset.prod_map]
  rfl

include well hs fund book inside hi tag in
theorem observed (simple:G.Simple)(r d:ℕ)(kept:d≤r)(s:Finset T):
    let cut:=retain R i per T s
    let W:=staged B R N i per hi F tag h x (bank) a r
    (Order.observe (J₁) r (Order.ratio W) d).part (face cut)=
      (∏u∈cut,(c₁) u)*(MvPolynomial.eval (flatten a)
        (coeff d (income (k:=k) B old q root y t R N i per F h T s)):ℝ):=by
  intro cut W
  have norm:=WilsonReceivedDepositedOrbitalResponse.normalized B old q root y t R N i per hi F tag h well hs fund book
    inside x a simple r
  have coherent:=same B old q root y t R N i per hi F tag h well hs fund book inside T simple s
  rw [show Order.ratio W=_ from norm,coherent]
  exact WilsonReceivedDepositedOrbitalMode.read r (flatten a) (c₁) (fun S=>picked S) cut d kept

end YM.Integration.WilsonReceivedDepositedOrbitalProper
end
