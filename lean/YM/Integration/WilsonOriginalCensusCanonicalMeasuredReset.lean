import YM.Integration.WilsonOriginalCensusCanonicalKinetic
import YM.Integration.WilsonCapturedPrimaryWeakTrialClockReversion
import YM.Integration.WilsonOriginalRawQReversion

/-! The original measured clock on each compatible connected face of the
canonical first edge, with the scalar and each source's own wallet. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusCanonicalMeasuredReset
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
open WilsonOriginalEarnedUnaryDriver (driver)
open WilsonCoeffUV.Winding WilsonCoeffUV.Power Next.Rank
open FreeResolvent
open WilsonOriginalChargedForestQ WilsonVacuumPreResetFiniteRegister
open WilsonCapturedPrimaryWindingVerseRoster (coefficient)
variable {G:Gauge} {V:Type} [Fintype V] [DecidableEq V] (R:Run G)(d:V→ℕ){h:V→ℕ}(pt:V→Chamber)
  (q:(j:V)→Choice R d j)(N i per:ℕ)(hi:i<N)
  (F:Forest (step R i per).ratio)(tag:(step R i per).Choices)
  (x:Affinity.Wallet (WilsonOriginalMixedBlockRows.room V)) {n:Side}(a:Fin (Pages n (fine R i per))→V→Lattice.Cover)
local notation "J" => Stock.census V
local notation "K" => model R N i per hi
local notation "S" => step R i per
local notation "f" => fine R i per
local notation "A" => saddle R N i per F
local notation "ρ" => fderiv ℝ ((K).b F) 0
local notation "κ" => (fun j=>contact (h j))
local notation "φ" => relative R N i per hi F (covered R N i per)
local notation "badge" => (fun j:V=>(J).fire j)
local notation "c" => (fun j:V=>(x j).val)

open WilsonVacuumPreResetStationaryChange WilsonOriginalFoldedMarkedRightColumn WilsonCoeffUV.Mer
open WilsonReceivedCanonicalVerseRegister WilsonReceivedCanonicalVerseBasis


open WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Mer
open WilsonOriginalCensusCanonicalPageFold (localOn folded)
open WilsonReceivedDepositedOrbitalGrade (booked)
local notation "front" y:max => WilsonReceivedCanonicalVerseRegister.start R d (κ) pt q y
local notation "γ" => ratioHigh (levels R) R.metals.O N i
local notation "terms" => WilsonOriginalCensusCanonicalFront.normalized (h:=h) (n:=n) R d pt q N i per F a


open RG16 RG16.Literal Pert.Asymptotics Next.Scheduling Next.Scheduling.Clock
open AnalyticBridge VerifiedReset ConnectedActivityE6 PhysicalNext Repeat Progress.DirectedRecipe Payments
open AllOrder.Transit WheelP AllOrder.Floe.Step PlanV Pane ThroughLaunch Roost Legato Graces Extra.Trajectories
open LocalLTE.Weft FormalBulk08
open WilsonOriginalRawQReversion (dated coordinates)
open WilsonVacuumPreResetMeasuredCoin (Agrees)
open WilsonReceivedDepositedOrbitalMode (face)
local notation "cum" t:max => WilsonOriginalCensusCanonicalKinetic.connected (h:=h) R d pt q N i per F t
local notation "Z" => coarse R i per

def hearing (p:ℕ)(s:Finset V)(j:ℕ)(b:Stationary.Link G (Z)):ℂ:=
  let angular:=Stationary.arm G _ 1 b
  let full:=WilsonOriginalCensusCanonicalMoments.moments (h:=h) (n:=n) R d pt q N i per F x a angular p
  (Order.observe (J) p (Extra.Trajectories.connected full) j).part (face s)

local notation "reads" => hearing (h:=h) (n:=n) R d pt q N i per F x a

include hi
theorem held (simple:G.Simple)(p:ℕ)(s:Finset V)(e:ℕ)(he:e≤p)(b:Stationary.Link G (Z)):
    (reads) p s e b=(∏j∈s,(x j).val)*WilsonNeutralSignedPolynomialRate.read (coordinates G (Z))
      (folded a (cum 1) s) e b:=by
  let angular:=Stationary.arm G _ 1 b
  change (Order.observe (J) p (Extra.Trajectories.connected (WilsonOriginalCensusCanonicalMoments.moments
    (h:=h) (n:=n) R d pt q N i per F x a angular p)) e).part (face s)=_
  rw [WilsonOriginalCensusCanonicalKinetic.entrance (h:=h) (n:=n) R d pt q N i per hi F x a simple angular p]
  exact WilsonReceivedDepositedOrbitalMode.read p (flatten angular) (c) (folded a (cum 1)) s e he

theorem original {m level:ℕ}{quiet:ℕ→SeriesA G}{π:ℕ→Layout G}{Γ:ℕ→Pace.Coin}
    (course:Agrees R N m level quiet π Γ)(hm : m ≤ i)(starts:Γ i 0=0)(simple:G.Simple)
    (p:ℕ)(hp:p≤level+2)(s:Finset V)(e:ℕ)(he:e≤p)(b:Stationary.Link G (Z)):
    Adjacent.born ((reads) p s) ((Rebirth.caliber (Γ i) starts).back (level+2)) 0 p e b=
      (∏j∈s,(x j).val)*WilsonNeutralSignedPolynomialRate.read (coordinates G (Z))
        (folded a (cum (γ)) s) e b:=by
  let gross:=∏j∈s,(x j).val
  have fare:=(WilsonVacuumPreResetMeasuredCaliber.settled R course hm hi starts).2.2.2
  have paid:Adjacent.born ((reads) p s) ((Rebirth.caliber (Γ i) starts).back (level+2)) 0 p e b=
      gross*WilsonNeutralSignedPolynomialRate.read (coordinates G (Z))
        (Wine.canter (Wine.bookH (dated R N i)) (Wine.bookU (dated R N i)) (Woods G (Z))
          (folded a (cum 1) s)) e b:=by
    simpa only [dated] using (WilsonNeutralSignedPolynomialRate.original fare ((reads) p s) (coordinates G (Z))
      (folded a (cum 1) s) (he.trans hp) he b gross (fun j hj t=>
        held (h:=h) (n:=n) R d pt q N i per hi F x a simple p s j hj (t • b)))
  have unit:PowerSeries.constantCoeff (dated R N i)=1:=angle_tilt
    simple R.alloy.B.ratio hi
  rw [WilsonCapturedPrimaryWeakTrialClockReversion.dated _ unit] at paid
  change _=gross*WilsonNeutralSignedPolynomialRate.read (coordinates G (Z))
    (redo (γ) (folded a (cum 1) s)) e b at paid
  rw [WilsonOriginalCensusCanonicalKinetic.restamp (h:=h) (n:=n) R d pt q N i per hi F a simple s] at paid
  exact paid

end YM.Integration.WilsonOriginalCensusCanonicalMeasuredReset
end
