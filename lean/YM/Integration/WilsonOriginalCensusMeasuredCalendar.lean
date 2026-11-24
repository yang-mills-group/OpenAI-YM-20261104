import YM.Integration.WilsonOriginalCensusMeasuredStation

/-! A single period tail for all actual dates, proper faces and test charts of
one finite marked program. The upper cutoff and all true posts come afterwards. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusMeasuredCalendar
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
open Filter Finset Marker Multi WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Address
open WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Wheel.Express
open WilsonCoeffUV.Embroider WilsonCoeffUV.Bank.Carp
open Work.F08 OriginalMarkedSourceComet
open WilsonOriginalCensusMeasuredStation
open scoped Classical BigOperators

theorem reindexed {G:Gauge}{n i K q per diameter:ℕ}{D D':Fin n→ℕ}
    (R:Run G)(κ:(v:Fin n)→Knob (D v))(κ':(v:Fin n)→Knob (D' v))(pt:Fin n→Chamber)
    (k:Fin n→ℕ)(C:Fin n→ℝ)(amount:ℝ)(chart:D'=D)(knobs:HEq κ' κ)
    (paid:CreditAt R κ pt k C i K q per diameter amount):
    CreditAt R κ' pt k C i K q per diameter amount:=by
  subst D'
  rw [eq_of_heq knobs]
  exact paid

theorem original {G:Gauge}{n q:ℕ}{D:Fin n→ℕ}(R:Run G)(κ:(v:Fin n)→Knob (D v))
    (pt:Fin n→Chamber)(simple:G.Simple)(quiet:WilsonReceivedCloseFundedHeat.Quiet R)
    (salary:ℕ→Gear G→ℝ)(priced:FundedMarkedCoverRows.prices salary R.kit)
    (k:Fin n→ℕ)(C:Fin n→ℝ)(positive:∀v,0 ≤ C v):
    ∀ᶠ b:ℕ in atTop,∀K:ℕ,
    let dates:Type:=↥(Ico b K)
    ∀school:dates→Realm G (q+1) Credit.leanC,
    (∀j, (school j).anchor ≤ j.val) → (∀j,(school j).draws=R.family.path.levels) →
    (∀j,(school j).paid=R.metals.O) →
    ∀(diameter:dates→ℕ)(amount:dates→Hot (Stock.census (Fin n))→ℝ),
    (∀j s,0<amount j s) →
    ∀ᶠ per:ℕ in atTop,∀j:dates,∀s:Hot (Stock.census (Fin n)),
      CreditAt R κ pt k C j.val K q per (diameter j) (amount j s):=by
  obtain ⟨b₀,h⟩:=eventually_atTop.1 (WilsonOriginalCensusMeasuredStation.select (q:=q)
    R κ pt simple quiet salary priced k C positive)
  filter_upwards [eventually_ge_atTop b₀] with b late
  intro K dates school anchor drawn bought diameter amount pos
  have all (j:dates)(s:Hot (Stock.census (Fin n))):∀ᶠ per:ℕ in atTop,
      CreditAt R κ pt k C j.val K q per (diameter j) (amount j s):=by
    have date:=Finset.mem_Ico.mp j.property
    exact h j.val (late.trans date.1) K date.2 (school j) (anchor j) (drawn j)
      (bought j) (diameter j) (amount j s) (pos j s)
  exact Filter.eventually_all.2 fun j=>Filter.eventually_all.2 fun s=>all j s

end YM.Integration.WilsonOriginalCensusMeasuredCalendar
end
