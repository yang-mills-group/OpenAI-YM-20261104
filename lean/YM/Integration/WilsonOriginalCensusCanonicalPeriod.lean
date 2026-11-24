import YM.Integration.WilsonOriginalCensusCanonicalDeck
import YM.Integration.WilsonOriginalCensusCanonicalDigit
import YM.Integration.WilsonNeutralTwoPrintPathBoxLimit
import YM.Integration.WilsonNeutralTwoPrintPathBoxHome

/-! The relative images in a canonical first connected birth are summed before
the common deck mean. All period prices precede the upper Wilson cutoff. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusCanonicalPeriod
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


open WilsonOriginalCensusOrbitCenters (layout shifted)
open WilsonOriginalConnectedPeriodPage (Deck)
open WilsonOriginalCensusDeckMean (mean)
open WilsonNeutralTwoPrintPathPageSeason (high)

open WilsonReceivedFixedDigitIntake (next)
open WilsonCoeffUV.Wheel.Motion (steppedC ramble)
open private translated from YM.Integration.WilsonPointChildCenteredSeat

open WilsonNeutralTwoPrintPathStart (returned)
open WilsonReceivedFixedDigitCanonical (fixed)
open WilsonReceivedFixedDigitHistory (Digits)
open WilsonNeutralTwoPrintPathBoxMean (plotted)
open WilsonThermometerDeclaredSeeds
open OriginalMarkedSourceComet
open scoped Topology
variable (R:Run G)(k:I→ℕ)(κ:(v:I)→Knob (D v))(pt:I→Chamber)

def Actual (N i:ℕ)(seed:(v:I)→Choice R k v)(cells:Digits R.family.path.levels I)
    (J:Finset I)(a r:ℕ)(X:Side)(y:I → Cover):=
  returned R k κ pt N i X seed y (cells i) J a r

def Covered (N i:ℕ)(seed:(v:I)→Choice R k v)(cells:Digits R.family.path.levels I)
    (J:Finset I)(a r:ℕ)(y:I → Cover):=
  (fixed R k κ pt N (i+1) i cells seed y J).2 a r

theorem issued (simple:G.Simple)(sale:ℕ→Gear G→ℝ)(paid:FundedMarkedCoverRows.prices sale R.kit)(Q:ℕ):
    ∀ᶠ i:ℕ in atTop,∀(J:Finset I)(a r:ℕ),a≤Q → ∃C σ:ℝ,0≤C ∧ 0<σ ∧
    ∀N,i<N → ∀(seed:(v:I)→Choice R k v)(cells:Digits R.family.path.levels I)(X:Side)(y:I → Cover),
    MarkU y J (Actual R k κ pt N i seed cells J a r X y) (Covered R k κ pt N i seed cells J a r y) σ C:=by
  filter_upwards [WilsonNeutralTwoPrintPathStart.original R k κ pt simple sale paid Q] with i filed
  intro J a r grade
  obtain ⟨C,σ,pos,hs,hearing⟩:=filed J a r grade
  refine ⟨C,σ,pos,hs,?_⟩
  intro N live seed cells X y
  have stage:fixed R k κ pt N (i+1) i cells seed y J=
      logO R.family.path.levels R.metals.O i N
        (WilsonReceivedCanonicalVerseRegister.start R k κ pt seed (chartIn (loose R.family.path.levels i) y (cells i))) k J:=by
    unfold fixed
    rw [show i+1-i=1 by omega]
    rfl
  simpa only [Actual,Covered,stage] using hearing N live seed X y (cells i)

theorem finite (simple:G.Simple)(N i:ℕ)(live:i<N)(seed:(v:I)→Choice R k v)
    (cells:Digits R.family.path.levels I)(J:Finset I)(o:I)(member:o∈J)(a r:ℕ)
    {C σ:ℝ}(hs:0<σ)(cash:∀X y,MarkU y J (Actual R k κ pt N i seed cells J a r X y)
      (Covered R k κ pt N i seed cells J a r y) σ C)
    {n X:Side}(h:n.val∣X.val)(root:Site X)(site:(J.erase o)→Site X)(d:ℕ)
    (near:∀v,separation root (site v)≤d)(room:32*d<X.val)
    (test:Pen D J →L[ℝ] ℂ)(weights:(Fin r→Site n × Hooks G)→ℂ)(height:ℝ)(hp:0≤height)(bounded:∀x,‖weights x‖≤height):
    let P:=Actual R k κ pt N i seed cells J a r X
    let F:=Covered R k κ pt N i seed cells J a r
    let y₀:=layout h J o root site (retained h site)
    ‖mean h (plotted h J o root site P test weights) -
      ∑y:Fin r→Site n × Hooks G,test (plume (F y₀) n y)*weights y‖ ≤
      (Real.exp (-(((σ/2)/2)*((n.val:ℝ)-d))/2)*price J o (Hooks G) r σ (‖test‖*C) +
        ‖test‖*(tariff (Hooks G) r σ C*catchW (σ/512) X))*height:=by
  intro P F y₀
  rw [←WilsonOriginalCensusDeckMean.constant h (∑y:Fin r→Site n × Hooks G,test (plume (F y₀) n y)*weights y)]
  apply WilsonOriginalCensusDeckMean.paid
  intro w
  have moved(v:J.erase o):separation (w.val+root) (shifted h site w v)≤d:=by
    change separation (w.val+root) (w.val+site v)≤d
    simpa only [add_comm w.val,separation_translate] using near v
  let rows:=fun (p:(J.erase o)→Fin (Pages n X))=>P (layout h J o (w.val+root) (shifted h site w) p)
  have source:=WilsonNeutralTwoPrintPathPageHearing.original h J o member (w.val+root) (shifted h site w)
    d moved room σ C hs test rows F (fun p=>cash X _) weights height hp bounded
  have center:=WilsonOriginalCensusCanonicalDeck.center (fixed R k κ pt N (i+1) i cells seed)
    (WilsonNeutralTwoPrintPathOldMotion.original R k κ pt simple N (i+1) i (by omega) (by omega) cells seed)
    J a r h o root site w
  change plume (F (layout h J o (w.val+root) (shifted h site w) (retained h (shifted h site w)))) n=plume (F y₀) n at center
  dsimp only at source
  change ‖plotted h J o root site P test weights w -
    ∑y:Fin r→Site n × Hooks G,test (plume (F (layout h J o (w.val+root) (shifted h site w)
      (retained h (shifted h site w)))) n y)*weights y‖≤_ at source
  rw [center] at source
  exact source

end YM.Integration.WilsonOriginalCensusCanonicalPeriod
end
