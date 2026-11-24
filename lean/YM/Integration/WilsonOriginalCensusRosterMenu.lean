import YM.Integration.WilsonOriginalCensusSituatedRank

/-! One physical period opening pays every retained coupling and angular index on every actual
    group of binder names. The compensated input, child and held field are quantified later. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusRosterMenu
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
variable {G:Gauge}{e v:ℕ}{D k:Fin v→ℕ}{I:Type}[Fintype I][DecidableEq I]{H:I→ℕ}


open Filter WilsonCoeffUV.Winding
open scoped Topology


open WilsonReceivedFixedDigitCanonical (fixed)
open WilsonReceivedFixedDigitHistory (Digits)
open WilsonThermometerDeclaredSeeds OriginalMarkedSourceComet
open WilsonNeutralTwoPrintPathCalendar (spent)
open WilsonNeutralTwoPrintPathBoxMean (plotted)


open WilsonNeutralTwoPrintPathBoxPlacement (homes)
open WilsonNeutralTwoPrintPathBoxInk (ink)
open WilsonNeutralTwoPrintPathBoxHome (breadth)
open WilsonReceivedFixedDigitIntake (next)

open WilsonReceivedDepositedOrbitalFixedMoments (program reading)
open WilsonIndependentCollarOrbitalPeg (outer)
open WilsonIndependentCollarAngularPeg (multiplier)

open WilsonIndependentCollarOrbitalReception (relative)

/-- The genuinely returned normalized conditional at one angular rank on the repeated board. -/
def sheets (R:Run G)(ranks:I→ℕ)(N m q:ℕ)(grid:Side)(old:Outerm G (fun _:I=>1))
    (digit:I→Site (loose R.family.path.levels m).L)(J:Finset I)(o:I)(place:I→ Cover)(a r:ℕ)
    (Z:Stationary.Link G grid)(u:Covers R.family.path.levels.S m grid):ℂ:=
  let X:=R.family.side m u.val
  let previous:=fun y=>spent R ranks N m q X old y digit J a r
  mean u.prop (plotted u.prop J o (wrap X (place o)) (homes X (place o) (relative J o place))
    previous (outer J) (multiplier Z))

/-- The same finite conditional on the physical board at the registered relative positions. -/
def central (R:Run G)(ranks:I→ℕ)(N m q:ℕ)(grid:Side)(old:Outerm G (fun _:I=>1))
    (digit:I→Site (loose R.family.path.levels m).L)(J:Finset I)(o:I)(place:I→ Cover)(a r:ℕ)
    (Z:Stationary.Link G grid):ℂ:=
  let previous:=spent R ranks N m q grid old (ink J o (place o) (relative J o place)) digit J a r
  Complex.ofReal (MvPolynomial.eval (WilsonOriginalRawQReversion.coordinates G grid Z)
    (paint r (fun z=>touch reading J (previous z))))

def Paid (R:Run G)(κ:(i:Fin v)→Knob (D i))(pt:Fin v→Chamber)(m K q per:ℕ)
    (words:I→Finset (Fin v))(front:I→Fin v)(C:Fin v→ℝ)(d:ℕ)(ε:ℝ)
    (J:Finset I)(o:I)(a r:ℕ):Prop:=
  ∀N,K ≤ N → ∀(seed:(v:Fin v)→Choice R k v)(cells:Digits R.family.path.levels (Fin v))
    (sites:Fin v→ Cover)(t:Case D),(∀v,‖t v‖ ≤ C v) →
  ∀(grid:Side),(R.family.side m per).val∣grid.val → ∀(digit:I→Site (loose R.family.path.levels m).L)
    (place:I→ Cover), breadth J o 0 (relative J o place) ≤ d →
  ∀(Z:Stationary.Link G grid),‖Z‖ ≤ 1 →
    let Y:=fixed R k κ pt N K (m+1) cells seed
    let old:=program (k:=k) Y q words front (fun _=>sites) (fun _=>t)
    let ranks:=fun i=>mass k (words i)
    let high:=sheets R ranks N m q grid old digit J o place a r Z
    let value:=central R ranks N m q grid old digit J o place a r Z
    let L:=coverFilter R.family.path.levels.S m grid
    Tendsto high L (𝓝 (limUnder L high)) ∧ ‖limUnder L high-value‖ ≤ ε

theorem original (R:Run G)(κ:(i:Fin v)→Knob (D i))(pt:Fin v→Chamber)(simple:G.Simple)
    (quiet:WilsonReceivedCloseFundedHeat.Quiet R)(salary:ℕ→Gear G→ℝ)(bought:FundedMarkedCoverRows.prices salary R.kit)
    (words:I→Finset (Fin v))(front:I→Fin v)(named:∀i,front i∈words i)(C:Fin v→ℝ)(nonneg:∀i,0 ≤ C i):
    ∀ᶠ m:ℕ in atTop,∀K,m<K →
    ∀(Q:Realm G (e+1) Credit.leanC),Q.anchor ≤ m → Q.draws=R.family.path.levels → Q.paid=R.metals.O →
    ∀(maxRank diameter:ℕ)(ε:ℝ),0 < ε →
    ∀ᶠ per:ℕ in atTop,∀J:Finset I,∀o:J,∀a:Fin (e+1),∀r:Fin (maxRank+1),
      Paid (k:=k) R κ pt m K e per words front C diameter ε J o.val a.val r.val:=by
  filter_upwards [WilsonOriginalCensusSituatedRank.original (e:=e) (k:=k) R κ pt simple quiet salary bought
    words front named C nonneg] with m issued
  intro K finer Q admit draw coin maxRank diameter ε small
  refine eventually_all.2 fun J=>eventually_all.2 fun o=>eventually_all.2 fun a=>eventually_all.2 fun r=>?_
  filter_upwards [issued K finer Q admit draw coin J o.val o.property a.val r.val (by omega) diameter ε small] with per paid
  intro N top seed cells sites t widths grid divides digit place fits Z bounded
  have atRank:=paid N top seed cells sites t widths grid divides digit place fits Z bounded
  let L:=coverFilter R.family.path.levels.S m grid
  letI:NeBot L:=coverFilter_neBot R.kit.floor m grid
  dsimp only at atRank ⊢
  refine ⟨?_,atRank.2.1⟩
  exact atRank.1.limUnder_eq.symm ▸ atRank.1

end YM.Integration.WilsonOriginalCensusRosterMenu
end
