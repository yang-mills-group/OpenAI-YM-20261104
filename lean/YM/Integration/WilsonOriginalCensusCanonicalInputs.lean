import YM.Integration.WilsonReceivedCanonicalSocketWick
import YM.Integration.WilsonOriginalMixedBlockRows

/-! The canonical finite-stencil Wick inputs at their own addresses, with the
original nonlinear vacuum, covariance and source wallet on every copied page. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusCanonicalInputs
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
variable {G:Gauge} {V:Type} [Fintype V] [DecidableEq V]
  (R:Run G) (d:V→ℕ) {h:V→ℕ} (pt:V→Chamber) (q:(j:V)→Choice R d j)
  (N i per:ℕ) (hi:i<N) (F:Forest (step R i per).ratio)
  (x:Affinity.Wallet (WilsonOriginalMixedBlockRows.room V))
  (B:fieldDir G (coarse R i per) 1) (z:Precision.Key F G→ℝ)

local notation "S" => step R i per
local notation "K" => model R N i per hi
local notation "A" => saddle R N i per F
local notation "ρ" => fderiv ℝ ((K).b F) 0
local notation "κ" => (fun j=>contact (h j))
local notation "f" => fine R i per
local notation "J" => Stock.census V

def inlet (a:V→Lattice.Cover) (j:V):Ink ((Active G F)⊕Woods G (coarse R i per)):=
  SignedMeasuredSourceSeries.probe (S) F (A) (ρ)
    (readO (present h) (WilsonReceivedCanonicalVerseRegister.start R d κ pt q a {j}) (f))

variable {n:Side} (addresses:Fin (Pages n (fine R i per))→V→Lattice.Cover)

def seed (p:Fin (Pages n (fine R i per)))(j:V)(grade:ℕ):ℂ:=
  let X:=WilsonReceivedCanonicalVerseRegister.start R d κ pt q (addresses p)
  let ray:=SignedMeasuredSourceSeries.probe (S) F (A) (ρ) (WilsonCoeffUV.Wheel.Mark.readO (present h) (X {j}) (fine R i per))
  ↑(MvPolynomial.eval (SignedRegisteredKernelPolynomial.focus F B z) (coeff grade ray):ℝ)

def value (r:ℕ)(s:Hot (Board (J) r)):ℂ:=
  let grade:=(Join.right s.val).val.card
  (grade.factorial:ℂ)*(if (Join.left s.val).val.Nonempty then
    ∑p:Fin (Pages n (fine R i per)),∑j:V,if (J).fire j=Join.left s.val then (x j).val*
      seed (h:=h) R d pt q N i per hi F B z addresses p j grade else 0
    else Cloud.paint z (SignedRegisteredMarkedProgram.register F B
      (coeff grade (relative R N i per hi F (covered R N i per)))))

end YM.Integration.WilsonOriginalCensusCanonicalInputs
end
