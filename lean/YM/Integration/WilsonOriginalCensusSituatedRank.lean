import YM.Integration.WilsonOriginalCensusTranslatedWinding
import YM.Integration.WilsonIndependentCollarOrbitalReception

/-! The genuine angular response to any translated configuration of fronts of bounded
    relative diameter. The physical period threshold precedes the fronts, the ultraviolet
    cutoff and the held Wilson link. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusSituatedRank
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

theorem original (R:Run G)(κ:(i:Fin v)→Knob (D i))(pt:Fin v→Chamber)(simple:G.Simple)
    (quiet:WilsonReceivedCloseFundedHeat.Quiet R)(salary:ℕ→Gear G→ℝ)(bought:FundedMarkedCoverRows.prices salary R.kit)
    (words:I→Finset (Fin v))(front:I→Fin v)(named:∀i,front i∈words i)(C:Fin v→ℝ)(fees:∀v,0 ≤ C v):
    ∀ᶠ m:ℕ in atTop,∀K,m<K →
    ∀(Q:Realm G (e+1) Credit.leanC),Q.anchor ≤ m → Q.draws=R.family.path.levels → Q.paid=R.metals.O →
    ∀(J:Finset I)(o:I),o∈J → ∀a r,a ≤ e → ∀(d:ℕ)(ε:ℝ),0 < ε →
    ∀ᶠ per:ℕ in atTop,∀N,K ≤ N → ∀(seed:(i:Fin v)→Choice R k i)(cells:Digits R.family.path.levels (Fin v))
       (sites:Fin v→ Cover)(t:Case D), (∀v,‖t v‖ ≤ C v) →
    ∀(grid:Side),(R.family.side m per).val∣grid.val → ∀(digit:I→Site (loose R.family.path.levels m).L)
       (place:I→ Cover), breadth J o 0 (relative J o place) ≤ d →
    ∀(Z:Stationary.Link G grid),‖Z‖≤1 →
      let base:=relative J o place
      let Y:=fixed R k κ pt N K (m+1) cells seed
      let old:=program (k:=k) Y e words front (fun _=>sites) (fun _=>t)
      let ranks:=fun i=>mass k (words i)
      let F:=fun y=>(next R.family.path.levels R.metals.O m N ranks old digit y J).2 a r
      let prior (side:Side)(y:I→ Cover):=spent R ranks N m e side old y digit J a r
      let high:=fun u:Covers R.family.path.levels.S m grid=>
        let X:=R.family.side m u.val
        mean u.prop (plotted u.prop J o (wrap X (place o)) (homes X (place o) base) (prior X) (outer J) (multiplier Z))
      let low:=fun M=>WilsonNeutralTwoPrintPathBoxSweep.retained grid J o (place o) base M F (outer J) (multiplier Z)
      let finite:=Complex.ofReal (MvPolynomial.eval (WilsonOriginalRawQReversion.coordinates G grid Z)
        (paint r (fun z=>touch reading J (prior grid (ink J o (place o) base) z))))
      Tendsto high (coverFilter R.family.path.levels.S m grid) (𝓝 (limUnder atTop low)) ∧
      ‖limUnder (coverFilter R.family.path.levels.S m grid) high-finite‖ ≤ ε ∧
      ‖limUnder atTop low-finite‖ ≤ ε := by
  let W:=fun i=>∏v∈words i,C v
  have non : ∀i,0≤W i:=fun i=>prod_nonneg (fun v _=>fees v)
  filter_upwards [WilsonOriginalCensusTranslatedWinding.original (e:=e) (H:=fun _:I=>1) R κ pt simple quiet salary bought
    words front named W non] with m issued
  intro K age Q anchor draws metal J o used a r grade d ε pos
  filter_upwards [issued K age Q anchor draws metal J o used a r grade
    d 1 1 ε zero_le_one pos] with per pay
  intro N top seed cells sites t cap grid house digit place housed Z bounded
  let base:=relative J o place
  have inside(i:I):‖(touch t (words i)).smulRight WilsonReceivedDepositedOrbitalFixedMoments.point‖≤ W i :=
    (WilsonIndependentCollarOrbitalPeg.inner t (words i)).2.trans
      (prod_le_prod (fun _ _=>norm_nonneg _) (fun v _=>cap v))
  have paid:=pay N top seed cells (fun _=>sites) _ inside grid house digit (place o) base housed
    (outer J) (multiplier Z) (WilsonIndependentCollarOrbitalPeg.outer_cap J)
    (WilsonIndependentCollarAngularPeg.unit_cap Z bounded)
  dsimp only at paid ⊢
  rw [WilsonIndependentCollarAngularPeg.physical] at paid
  exact paid

end YM.Integration.WilsonOriginalCensusSituatedRank
end
