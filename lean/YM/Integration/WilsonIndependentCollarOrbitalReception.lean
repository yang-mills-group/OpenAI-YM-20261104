import YM.Integration.WilsonOriginalCensusCofinalWinding
import YM.Integration.WilsonIndependentCollarAngularPeg

/-! Compare the actual two copies of the promoted source on the retained physical direction, with the fixed cutoff chosen before the period. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonIndependentCollarOrbitalReception
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

def relative (J:Finset I)(o:I)(place:I→ Cover)(j:J.erase o) : Cover := place j-place o

omit [Fintype I] in
theorem at_front (J:Finset I)(o:I)(place:I→ Cover)(i:I)(present:i∈J) :
    ink J o (place o) (relative J o place) i=place i := by
  by_cases first:i=o
  · subst i
    simp [WilsonNeutralTwoPrintPathBoxInk.ink,WilsonCoeffUV.Wheel.Address.toe]
  · have inside:i∈J.erase o:=mem_erase.mpr ⟨first,present⟩
    simp [WilsonNeutralTwoPrintPathBoxInk.ink,WilsonCoeffUV.Wheel.Address.toe,first,inside,relative]

/-- Every original directional test in its paid ball is admitted after the
period is opened. Only the finitary positions of the occupied fronts enter
the period threshold. All previous words stay in the same fixed-K source. -/
theorem original (R:Run G)(κ:(i:Fin v)→Knob (D i))(pt:Fin v→Chamber)(simple:G.Simple)
    (quiet:WilsonReceivedCloseFundedHeat.Quiet R)(salary:ℕ→Gear G→ℝ)(bought:FundedMarkedCoverRows.prices salary R.kit)
    (words:I→Finset (Fin v))(front:I→Fin v)(named:∀i,front i∈words i)(C:Fin v→ℝ)(fees:∀v,0 ≤ C v):
    ∀ᶠ m:ℕ in atTop,∀K,m<K →
    ∀(Q:Realm G (e+1) Credit.leanC),Q.anchor ≤ m → Q.draws=R.family.path.levels → Q.paid=R.metals.O →
    ∀(J:Finset I)(o:I),o∈J → ∀a r,a ≤ e → ∀(place:I→ Cover)(ε:ℝ),0 < ε →
    ∀ᶠ per:ℕ in atTop,∀N,K ≤ N → ∀(seed:(i:Fin v)→Choice R k i)(cells:Digits R.family.path.levels (Fin v))
       (sites:Fin v→ Cover)(t:Case D), (∀v,‖t v‖ ≤ C v) →
    ∀(grid:Side),(R.family.side m per).val∣grid.val → ∀(digit:I→Site (loose R.family.path.levels m).L)
       (Z:Stationary.Link G grid),‖Z‖≤1 →
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
  filter_upwards [WilsonOriginalCensusCofinalWinding.original (e:=e) (H:=fun _:I=>1) R κ pt simple quiet salary bought
    words front named W non] with m issued
  intro K age Q anchor draws metal J o used a r grade place ε pos
  let base:=relative J o place
  filter_upwards [issued K age Q anchor draws metal J o used a r grade
    (breadth J o (place o) base) 1 1 ε zero_le_one pos] with per pay
  intro N top seed cells sites t cap grid house digit Z bounded
  have inside(i:I):‖(touch t (words i)).smulRight WilsonReceivedDepositedOrbitalFixedMoments.point‖≤ W i :=
    (WilsonIndependentCollarOrbitalPeg.inner t (words i)).2.trans
      (prod_le_prod (fun _ _=>norm_nonneg _) (fun v _=>cap v))
  have paid:=pay N top seed cells (fun _=>sites) _ inside grid house digit (place o) base le_rfl
    (outer J) (multiplier Z) (WilsonIndependentCollarOrbitalPeg.outer_cap J)
    (WilsonIndependentCollarAngularPeg.unit_cap Z bounded)
  dsimp only at paid ⊢
  rw [WilsonIndependentCollarAngularPeg.physical] at paid
  exact paid

end YM.Integration.WilsonIndependentCollarOrbitalReception
end
