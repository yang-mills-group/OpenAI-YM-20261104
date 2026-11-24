import YM.Integration.WilsonOriginalCensusRosterFare

/-! A common original period floor serves every possible enrolled binder footprint, before
    the ultraviolet cutoff, physical placements, case directions and true seats are read. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusRosterOpening
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


open WilsonOriginalCensusRosterMenu (Paid sheets central)
open WilsonOriginalCensusRosterFare (whole)
open WilsonOriginalMixedBlockRows (room)
open QuadraticLocal QuadraticLocal.Earn

def Patterns (I:Type)(v:ℕ):= {p:(I→Finset (Fin v))×(I→Fin v) // ∀i,p.2 i∈p.1 i}

noncomputable instance (I:Type)[Fintype I](v:ℕ) : Fintype (Patterns I v):=by
  unfold Patterns
  exact Fintype.ofFinite _

def opening (R:Run G)(κ:(v:Fin v)→Knob (D v))(pt:Fin v→Chamber)(k:Fin v→ℕ)
    (C:Fin v→ℝ)(m K q per maxRank diameter:ℕ)(ε:ℝ):Prop:=
  ∀p:Patterns I v,∀J:Finset I,∀o:J,∀a:Fin (q+1),∀r:Fin (maxRank+1),
      Paid (k:=k) R κ pt m K q per p.val.1 p.val.2 C diameter ε J o.val a.val r.val

theorem original (R:Run G)(κ:(i:Fin v)→Knob (D i))(pt:Fin v→Chamber)(simple:G.Simple)
    (quiet:WilsonReceivedCloseFundedHeat.Quiet R)(salary:ℕ→Gear G→ℝ)(bought:FundedMarkedCoverRows.prices salary R.kit)
    (C:Fin v→ℝ)(nonneg:∀v,0 ≤ C v):
    ∀ᶠ m:ℕ in atTop,∀K,m<K →
    ∀(Q:Realm G (e+1) Credit.leanC),Q.anchor ≤ m → Q.draws=R.family.path.levels → Q.paid=R.metals.O →
    ∀(maxRank diameter:ℕ)(ε:ℝ),0 < ε →
    ∀ᶠ per:ℕ in atTop,opening (I:=I) R κ pt k C m K e per maxRank diameter ε:=by
  have all:=fun p:Patterns I v=>WilsonOriginalCensusRosterMenu.original (e:=e) (k:=k) R κ pt simple quiet salary
    bought p.val.1 p.val.2 p.prop C nonneg
  filter_upwards [Filter.eventually_all.2 all] with m issues
  intro K finer Q admit shape cash maxRank diameter ε pos
  exact Filter.eventually_all.2 fun p=>issues p K finer Q admit shape cash maxRank diameter ε pos

omit [DecidableEq I] in
theorem orderBound (k:Fin v→ℕ)(w:I→Finset (Fin v))(s:Finset I)(a q:ℕ)(ha:a≤q):
    mass (fun i=>mass k (w i)) s+a ≤ Fintype.card I*mass k Finset.univ+q:=by
  apply Nat.add_le_add _ ha
  calc
    _ ≤ ∑_i∈s,mass k Finset.univ:=by
      apply Finset.sum_le_sum
      intro i hi
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ (w i))
    _ = s.card*mass k Finset.univ:=by simp
    _ ≤ _:=Nat.mul_le_mul_right _ (Finset.card_le_univ _)

end YM.Integration.WilsonOriginalCensusRosterOpening
end
