import YM.Integration.WilsonOriginalCensusOrbitCenters
import YM.Integration.WilsonOriginalCensusDeckMean
import YM.Integration.WilsonNeutralTwoPrintPathPageHearing
import YM.Integration.WilsonNeutralTwoPrintPathPageSeason

/-! The native angular hearing on all relative choices of the prior connected
words, with one common page volume and the original Wilson quiet at the appointment. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusOrbitHearing
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


open WilsonOriginalCensusOrbitCenters (shifted layout)
open WilsonOriginalConnectedPeriodPage (Deck)
open WilsonOriginalCensusDeckMean (mean)
open WilsonNeutralTwoPrintPathPageSeason (high)

theorem original (Q:Realm G (e+1) Credit.leanC)(m:ℕ)(admit:Q.anchor ≤ m)
    (J:Finset I)(a r:ℕ)(grade:a ≤ e){s:ℝ}(width:0<s):
    ∃C σ:ℝ,0 ≤ C ∧ 0<σ ∧ ∀N,m<N → ∀(n X:Side)(h:n.val∣X.val)
      (Y:Outerm G D)(A:ℝ),1 ≤ A → Wellness k Y → CoverBill Y e s A →
      ∀(b:I→Site (loose Q.draws m).L)(o:I)(_live:o∈J)(root:Site X)(site:(J.erase o)→Site X)
       (d:ℕ), (∀v,separation root (site v) ≤ d) → 32*d<X.val →
      ∀(test:Pen D J →L[ℝ] ℂ)(weights:(Fin r→Site n × Hooks G)→ℂ)(height:ℝ),
      0 ≤ height → (∀x,‖weights x‖ ≤ height) →
      let pos:=fun (w:WilsonOriginalConnectedPeriodPage.Deck h)=>layout h J o (w.val+root) (shifted h site w)
      let row:=fun (w:WilsonOriginalConnectedPeriodPage.Deck h)(p:(J.erase o)→Fin (Pages n X))=>
        high k e Q.draws Q.paid N m X J Y (pos w p) b a r
      let ledger:=fun (y:I → Cover)=>(logO Q.draws Q.paid m N
        (submit Y k e (chartIn (loose Q.draws m) y b)) k J).2 a r
      let plotted:=fun (w:WilsonOriginalConnectedPeriodPage.Deck h)=>∑x:Fin r→Site X × Hooks G,
        (∑p,test (row w p x))*weights (WilsonNeutralTwoPrintPathPageRead.lower h ∘ x)
      let reported:=fun (w:WilsonOriginalConnectedPeriodPage.Deck h)=>∑y:Fin r→Site n × Hooks G,
        test (plume (ledger (pos w (retained h (shifted h site w)))) n y)*weights y
      ‖mean h plotted-mean h reported‖ ≤ 
        (Real.exp (-(((σ/2)/2)*((n.val:ℝ)-d))/2)*price J o (Hooks G) r σ (‖test‖*(C*A^J.card))+
          ‖test‖*(tariff (Hooks G) r σ (C*A^J.card)*catchW (σ/512) X))*height:=by
  obtain ⟨C,σ,hC,hσ,sold⟩:=WilsonNeutralTwoPrintPathTariff.submitted (D:=D) (k:=k) Q m admit J a r grade width
  refine ⟨C,σ,hC,hσ,?_⟩
  intro N live n X h Y A hA law funded b o member root site d near room test weights height hp bounded pos row ledger plotted reported
  apply WilsonOriginalCensusDeckMean.paid
  intro w
  have close(v:J.erase o):separation (w.val+root) (shifted h site w v) ≤ d:=by
    change separation (w.val+root) (w.val+site v) ≤ d
    simpa only [add_comm w.val,separation_translate] using near v
  exact WilsonNeutralTwoPrintPathPageHearing.original h J o member (w.val+root) (shifted h site w)
    d close room σ (C*A^J.card) hσ test (row w) ledger
    (fun p=>sold N live X Y A hA law funded (pos w p) b) weights height hp bounded

end YM.Integration.WilsonOriginalCensusOrbitHearing
end
