import YM.Integration.WilsonOriginalCensusCanonicalMeasuredReset

/-! Reading a smaller retained horizon leaves the same signed coefficients of
the original measured clock. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusCanonicalRetainedClock
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


local notation "reads" => WilsonOriginalCensusCanonicalMeasuredReset.hearing (h:=h) (n:=n) R d pt q N i per F x a

private theorem restricted {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](U₁ U₂:Adjacent.Display E)
    (cost:Adjacent.UnitCost)(r e:ℕ)(b:E)(same:∀ j≤r,U₁ j=U₂ j):
    Adjacent.born U₁ cost 0 r e b=Adjacent.born U₂ cost 0 r e b:=by
  unfold Adjacent.born
  congr 1
  funext v
  unfold Adjacent.ages Adjacent.cover
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [same j (by simpa using mem_range.mp hj)]

include hi in
theorem original {m level:ℕ}{quiet:ℕ→SeriesA G}{π:ℕ→Layout G}{Γ:ℕ→Pace.Coin}
    (course:Agrees R N m level quiet π Γ)(hm : m ≤ i)(starts:Γ i 0=0)(simple:G.Simple)
    (order r e:ℕ)(hr:r≤order)(authorized:r≤level+2)(he:e≤r)(s:Finset V)(b:Stationary.Link G (Z)):
    Adjacent.born ((reads) order s) ((Rebirth.caliber (Γ i) starts).back (level+2)) 0 r e b=
      (∏j∈s,(x j).val)*WilsonNeutralSignedPolynomialRate.read (coordinates G (Z))
        (folded a (cum (γ)) s) e b:=by
  have same (j:ℕ)(hj:j≤r):(reads) order s j=(reads) r s j:=by
    funext z
    rw [WilsonOriginalCensusCanonicalMeasuredReset.held (h:=h) R d pt q N i per hi F x a simple order s j (hj.trans hr),
      WilsonOriginalCensusCanonicalMeasuredReset.held (h:=h) R d pt q N i per hi F x a simple r s j hj]
  rw [restricted _ _ _ r e b same]
  exact WilsonOriginalCensusCanonicalMeasuredReset.original (h:=h) R d pt q N i per hi F x a
    course hm starts simple r authorized s e he b

end YM.Integration.WilsonOriginalCensusCanonicalRetainedClock
end
