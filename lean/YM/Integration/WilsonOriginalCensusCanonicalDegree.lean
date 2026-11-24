import YM.Integration.WilsonOriginalCensusCanonicalMeasuredReset
import YM.Integration.WilsonReceivedDepositedOrbitalPortraitDegree

/-! A cutoff-independent angular-degree bound for an entire first-edge public
face. It remains valid as the number of deck assignments changes. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusCanonicalDegree
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


local notation "forest" => repeatF (S)
local notation "entry" => WilsonOriginalCensusCanonicalKinetic.connected (h:=h) R d pt q N i per (forest) 1
local notation "reads" => WilsonOriginalCensusCanonicalMeasuredReset.hearing (h:=h) (n:=n) R d pt q N i per (forest) x a
open WilsonOriginalCensusCanonicalPageFold (onFace)
open WilsonNeutralSignedPolynomialRate (read)
open Comparison.RG02.Valence

include hi in
theorem original (simple:G.Simple)(p:ℕ)(s:Finset V)(e:ℕ)(he:e≤p):
    Valence.Level ((mass d s+e:ℕ):ℤ) ((reads) p s e):=by
  let co:=coordinates G (Z)
  have expanded:((reads) p s e)=fun b=>(∏j∈s,(x j).val)*
      ∑v:s→Fin (Pages n (f)),read co ((entry) (onFace a s v) s) e b:=by
    funext b
    rw [WilsonOriginalCensusCanonicalMeasuredReset.held (h:=h) (n:=n) R d pt q N i per hi (forest) x a simple p s e he b]
    simp only [folded,WilsonNeutralSignedPolynomialRate.read,map_sum,Complex.ofReal_sum,co]
  rw [expanded]
  apply Valence.Level.factor
  apply Valence.Level.total
  intro v _
  let y:=onFace a s v
  have wage:Eu d (front y):=IndependentSourcePathFamily.legal _ y
    (fun j _=>WilsonReceivedCanonicalVerseBasis.grade R d (κ) pt j (q j))
  exact WilsonReceivedDepositedOrbitalPortraitDegree.original R N i per hi d (present h) simple (front y) wage 1 s e

end YM.Integration.WilsonOriginalCensusCanonicalDegree
end
