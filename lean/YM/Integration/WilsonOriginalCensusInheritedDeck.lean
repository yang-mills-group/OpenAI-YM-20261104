import YM.Integration.WilsonOriginalCensusOrbitCenters
import YM.Integration.WilsonNeutralTwoPrintPathInheritedMotion
import YM.Integration.WilsonNeutralTwoPrintPathItinerary

/-! A single original page translation preserves the full older covered
output on the physical board, including its field-independent value. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusInheritedDeck
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

open Further.PhysicalPeriodLimitF933 Macrame Shingle FVA1Physical TwoReset
open WilsonOriginalRelativePageTail (retained)
open WilsonPointChildRelativeLift (centers)
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Bank.Mosaic.Near WilsonCoeffUV.Blue
open WilsonNeutralTwoPrintPathPageLedger (price)
open WilsonNeutralTwoPrintPathRankFare (tariff)
open WilsonCoeffUV.Bank.Carp (plume)


open WilsonNeutralTwoPrintPathInheritedBlocks (gathered amount)
open WilsonOriginalCensusOrbitCenters (layout shifted)

open WilsonNeutralTwoPrintPathInherited (atom)
open WilsonReceivedFixedDigitIntake (next)
open scoped Classical BigOperators
variable {G:Gauge}{v e:ℕ}{D k:Fin v→ℕ}{I:Type}[Fintype I][DecidableEq I]{H:I→ℕ}

theorem center (L:Levels G)(O:ChartRatio G)(m N:ℕ)(live:m<N)(simple:G.Simple)(rat:LocalRatio O)
    (Y:Outerm G D)(well:Wellness k Y){s B:ℝ}(hs:0<s)(hB:1 ≤ B)(bill:CoverBill Y e s B)
    (words:I→Finset (Fin v))(front:I→Fin v)(named:∀i,front i∈words i)
    (sites:I→Fin v → Cover)(read:(i:I)→Pen D (words i) →L[ℝ] Vote (H i))
    (b:I→Site (loose L m).L)(J:Finset I)(a r:ℕ)(grade:a ≤ e)
    {n X:Side}(h:n.val∣X.val)(o:I)(root:Site X)(site:(J.erase o)→Site X)
    (w:WilsonOriginalConnectedPeriodPage.Deck h):
    let previous:=gathered Y k e words front sites read
    let mass₀:=fun i=>mass k (words i)
    let ledger:=fun (y:I → Cover)=>(logO L O m N
      (submit previous mass₀ e (chartIn (loose L m) y b)) mass₀ J).2 a r
    let origin:=layout h J o root site (retained h site)
    let moved:=layout h J o (w.val+root) (shifted h site w) (retained h (shifted h site w))
    plume (ledger moved) n=plume (ledger origin) n:=by
  intro previous mass₀ ledger origin moved
  obtain ⟨capital,valid,paid⟩:=WilsonNeutralTwoPrintPathInheritedBlocks.original Y well hs hB bill
    words front named sites read
  have book:=WilsonReceivedCompactVerseEntrance.original previous valid hs capital paid
  have printed(y:I → Cover):ledger y=(next L O m N mass₀ previous b y J).2 a r:=by
    let pos:=chartIn (loose L m) y b
    have term:=WilsonNeutralTwoPrintPathItinerary.step mass₀ L O N m
      (E:=submit previous mass₀ e pos) (W:=previous pos) (e:=e)
      (fun t g bound=>(book.2.2.1 pos t g bound).1) J a grade
    exact congrFun term r
  rw [printed,printed]
  let atoms (i:I):=atom Y k e (sites i) (words i) (front i) (read i)
  exact WilsonNeutralTwoPrintPathInheritedMotion.period L O m N live simple rat atoms valid b J
    origin moved (WilsonOriginalCensusOrbitCenters.motion h root w)
    (fun i _=>WilsonOriginalCensusOrbitCenters.center h J o root site w i)
    n (WilsonOriginalCensusOrbitCenters.period h root w) a r

end YM.Integration.WilsonOriginalCensusInheritedDeck
end
