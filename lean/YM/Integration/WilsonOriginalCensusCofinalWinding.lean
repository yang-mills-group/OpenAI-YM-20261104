import YM.Integration.WilsonOriginalCensusOrbitFixed
import YM.Integration.WilsonNeutralTwoPrintPathBoxHome

/-! The mean on the actual cofinal filter and the physical finite Wick response
    have the same tested limit as the physical period grows, uniformly above a fixed restart. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusCofinalWinding
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

theorem original (R:Run G)(κ:(i:Fin v)→Knob (D i))(pt:Fin v→Chamber)(simple:G.Simple)
    (quiet:WilsonReceivedCloseFundedHeat.Quiet R)(salary:ℕ→Gear G→ℝ)(bought:FundedMarkedCoverRows.prices salary R.kit)
    (words:I→Finset (Fin v))(front:I→Fin v)(named:∀i,front i∈words i)(W:I→ℝ)(pos:∀i,0 ≤ W i):
    ∀ᶠ m:ℕ in atTop,∀K,m<K →
    ∀(Q:Realm G (e+1) Credit.leanC),Q.anchor ≤ m → Q.draws=R.family.path.levels → Q.paid=R.metals.O →
    ∀(J:Finset I)(o:I),o∈J → ∀a r,a ≤ e → ∀d (U H₀ ε:ℝ),0 ≤ H₀ → 0 < ε →
    ∀ᶠ per:ℕ in atTop,∀N,K ≤ N → ∀(seed:(i:Fin v)→Choice R k i)(cells:Digits R.family.path.levels (Fin v))
      (sites:I→Fin v→ Cover)(read:(i:I)→Pen D (words i) →L[ℝ] Vote (H i)), (∀i,‖read i‖ ≤ W i) →
    ∀(grid:Side),(R.family.side m per).val∣grid.val → ∀(digit:I→Site (loose R.family.path.levels m).L)
      (origin:Cover)(base:(J.erase o)→ Cover), breadth J o origin base ≤ d →
    ∀(test:Pen H J →L[ℝ] ℂ)(weights:(Fin r→Site grid×Hooks G)→ℂ),‖test‖ ≤ U → (∀x,‖weights x‖ ≤ H₀) →
      let Y:=fixed R k κ pt N K (m+1) cells seed
      let old:=gathered Y k e words front sites read
      let ranks:=fun i=>mass k (words i)
      let F:=fun y=>(next R.family.path.levels R.metals.O m N ranks old digit y J).2 a r
      let prior (Z:Side)(y:I→ Cover):=spent R ranks N m e Z old y digit J a r
      let high:=fun u:Covers R.family.path.levels.S m grid=>
        let X:=R.family.side m u.val
        mean u.prop (plotted u.prop J o (wrap X origin) (homes X origin base) (prior X) test weights)
      let low:=fun M=>WilsonNeutralTwoPrintPathBoxSweep.retained grid J o origin base M F test weights
      let finite:=∑y:Fin r→Site grid×Hooks G,test (prior grid (ink J o origin base) y) * weights y
      Tendsto high (coverFilter R.family.path.levels.S m grid) (𝓝 (limUnder atTop low)) ∧
      ‖limUnder (coverFilter R.family.path.levels.S m grid) high-finite‖ ≤ ε ∧
      ‖limUnder atTop low-finite‖ ≤ ε:=by
  filter_upwards [WilsonOriginalCensusOrbitFixed.original (e:=e) (H:=H) R κ pt simple quiet salary bought words front named W,
    WilsonNeutralTwoPrintPathBoxReturn.original (D:=H) R k κ pt simple quiet salary bought words front named W pos e]
    with m opening returned
  intro K finer Q admit draw chart J o live a r grade d U H₀ ε hh small
  filter_upwards [opening K finer Q admit draw chart J o live a r grade d U H₀ ε hh small] with per earned
  intro N top seed cells sites read wages grid house digit origin base housed test weights cost bounded Y old ranks F prior high low finite
  letI:NeBot (coverFilter R.family.path.levels.S m grid):=coverFilter_neBot R.kit.floor m grid
  let X:=fun u:Covers R.family.path.levels.S m grid=>R.family.side m u.val
  have converge:=returned K finer J o live a r grade N top seed cells sites read wages grid digit origin base
    (fun u=>wrap (X u) origin) (fun u=>homes (X u) origin base)
    (fun u=>Macrame.branch u.prop _) (fun u i=>Macrame.branch u.prop _) test weights
  change Tendsto high _ (𝓝 (limUnder atTop low)) ∧ _ at converge
  refine ⟨converge.1,?_⟩
  have large:∀ᶠu:Covers R.family.path.levels.S m grid in coverFilter R.family.path.levels.S m grid,
      2*d < (X u).val:=(cover_size R.family.path.levels.S m grid).eventually (eventually_gt_atTop (2*d))
  have uniform:∀ᶠu in coverFilter R.family.path.levels.S m grid,‖high u-finite‖ ≤ ε:=by
    filter_upwards [large] with u room
    have fit:2*breadth J o origin base < (X u).val:=by omega
    obtain ⟨place,span⟩:=WilsonNeutralTwoPrintPathBoxHome.original u.prop J o origin base fit
    have price:=earned N top cells seed grid (X u) house u.prop sites read wages digit (wrap (X u) origin)
      (homes (X u) origin base) (fun i=>(span i).trans housed) test weights cost bounded
    dsimp only at price
    rw [place] at price
    exact price
  have paid:‖limUnder atTop low-finite‖ ≤ ε:=
    le_of_tendsto (converge.1.sub (tendsto_const_nhds (x:=finite))).norm uniform
  rw [converge.1.limUnder_eq]
  exact ⟨paid,paid⟩

end YM.Integration.WilsonOriginalCensusCofinalWinding
end
