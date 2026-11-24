import YM.Integration.WilsonOriginalCensusOrbitHearing
import YM.Integration.WilsonNeutralTwoPrintPathOldMotion
import YM.Integration.WilsonOriginalCensusOrbitCenters
import YM.Integration.WilsonOriginalCensusDeckMean
import YM.Integration.WilsonNeutralTwoPrintPathPageHearing
import YM.Integration.WilsonNeutralTwoPrintPathPageSeason

/-! A simultaneous deck translation of all canonical source sites has the same
finite physical reading after one actual normalized Gaussian step. -/
noncomputable section
namespace YM.Integration.WilsonOriginalCensusCanonicalDeck
open Work.F08 WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.Express WilsonCoeffUV.Wheel.Cadenza
open Function Filter Finset Lattice Wilson RG Precision Laurent WilsonCoeffUV Tree Bloch Exterior
open Next.Foundations PhysicalNext.Repeat.Legato
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer
open WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Bank.Realm
open WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Mosaic.Near WilsonCoeffUV.Blue WilsonCoeffUV.Soil
open WilsonCoeffUV.Embroider WilsonCoeffUV.Winding WilsonCoeffUV.Bank.Ticket
open WilsonReceivedDatedVerseReprint WilsonReceivedCompactVerseEntrance
open WilsonMarkedIndependentPhysicalIntake WilsonMarkedIndependentMixedGeometry
open AnalyticNext.QuarticMatch.Sheets IndependentSourcePathFamily
open scoped Classical BigOperators
variable {G:Gauge}{I:Type}[Fintype I][DecidableEq I]{D k:I→ℕ}{e:ℕ}

open Further.PhysicalPeriodLimitF933 Macrame Shingle FVA1Physical TwoReset
open WilsonOriginalRelativePageTail (retained)
open WilsonPointChildRelativeLift (centers)
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Bank.Mosaic.Near WilsonCoeffUV.Blue
open WilsonNeutralTwoPrintPathPageLedger (price)
open WilsonNeutralTwoPrintPathRankFare (tariff)
open WilsonCoeffUV.Bank.Carp (plume)


open WilsonOriginalCensusOrbitCenters (layout)
open WilsonOriginalConnectedPeriodPage (Deck)
open WilsonOriginalCensusDeckMean (mean)
open WilsonNeutralTwoPrintPathPageSeason (high)

open WilsonReceivedFixedDigitIntake (next)
open WilsonCoeffUV.Wheel.Motion (steppedC ramble)
open private translated from YM.Integration.WilsonPointChildCenteredSeat

omit [Fintype I] in
theorem center (Y:Outerm G D)(motion:∀v,ramble v Y)(J:Finset I)(a r:ℕ)
    {n X:Side}(h:n.val∣X.val)(o:I)(root:Site X)(site:(J.erase o)→Site X)
    (w:WilsonOriginalConnectedPeriodPage.Deck h):
    let origin:=layout h J o root site (retained h site)
    let others:=WilsonOriginalCensusOrbitCenters.shifted h site w
    let moved:=layout h J o (w.val+root) others (retained h others)
    plume ((Y moved J).2 a r) n=plume ((Y origin J).2 a r) n:=by
  intro origin others moved
  let v:=WilsonOriginalCensusOrbitCenters.motion h root w
  have same:moved=steppedC v origin:=funext (WilsonOriginalCensusOrbitCenters.center h J o root site w)
  have transported:Y moved J=WilsonCoeffUV.Mer.shifted (Y origin J) v:=by
    rw [same]
    exact congrFun (motion v origin) J
  rw [transported]
  change plume (revolve v _) n=_
  have hidden:wrap n v=0:=WilsonOriginalCensusOrbitCenters.period h root w
  rw [translated,hidden]
  funext x
  have sameKey:jog (-(0:Site n)) ∘ x=x:=by
    funext i
    ext <;> simp [jog]
  exact congrArg (plume ((Y origin J).2 a r) n) sameKey

end YM.Integration.WilsonOriginalCensusCanonicalDeck
end
