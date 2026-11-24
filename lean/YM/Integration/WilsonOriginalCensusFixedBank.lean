import YM.Integration.WilsonOriginalCensusOrbitFixed

/-! A strip and salary for the actual K-born prior, chosen before either regulator. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusFixedBank
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
open WilsonOriginalCensusDeckMean (mean)
open WilsonNeutralTwoPrintPathPageSeason (high)
open scoped Classical BigOperators
open Filter WilsonCoeffUV.Winding
open WilsonReceivedFixedDigitCanonical (fixed)
open WilsonReceivedFixedDigitHistory (Digits)
open WilsonThermometerDeclaredSeeds OriginalMarkedSourceComet
open scoped Topology

variable {G:Gauge}{n:ℕ}{D k:Fin n→ℕ}(R:Run G)
  (κ:(v:Fin n)→Knob (D v))(pt:Fin n→Chamber)

def Income (e i:ℕ):Prop:=
  ∀K,i<K → ∃σ A:ℝ,0<σ ∧ 1≤A ∧
    ∀N,K≤N → ∀(cells:Digits R.family.path.levels (Fin n))(seed:(v:Fin n)→Choice R k v),
      let Y:=fixed R k κ pt N K (i+1) cells seed
      Wellness k Y ∧ CoverBill Y e σ A

theorem original (simple:G.Simple)(quiet:WilsonReceivedCloseFundedHeat.Quiet R)
    (price:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices price R.kit)(e:ℕ):
    ∀ᶠi:ℕ in atTop,Income (k:=k) R κ pt e i:=by
  obtain ⟨_,_,seeds⟩:=WilsonReceivedCanonicalVerseRegister.original R k κ pt e (s:=1) zero_lt_one
  obtain ⟨start,calendar⟩:=eventually_atTop.1 (WilsonReceivedFixedDigitCanonical.original R k κ pt simple quiet price funded e)
  filter_upwards [eventually_ge_atTop start] with i later
  intro K top
  obtain ⟨σ,A,width,one,bank⟩:=calendar (i+1) (by omega) K top
  refine ⟨σ,A,width,one,?_⟩
  intro N live cells seed
  exact ⟨WilsonReceivedFixedDigitHistory.sound R.family.path.levels R.metals.O k N
      cells simple R.alloy.B.ratio _ (seeds seed).1 _ _ (by omega),
    fun sites J a ha r=>((bank N live 1 cells seed).1 sites J a ha r).access⟩

theorem transferred {tests:Fin n→ℕ}(matchTests:tests=D)(knob:(v:Fin n)→Knob (tests v))
    (same:HEq knob κ){e i:ℕ}(funds:Income (k:=k) R κ pt e i):
    Income (k:=k) R knob pt e i:=by
  subst tests
  cases eq_of_heq same
  exact funds

end YM.Integration.WilsonOriginalCensusFixedBank
end
