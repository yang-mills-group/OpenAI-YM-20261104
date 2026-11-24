import YM.Integration.WilsonVacuumPreResetFiniteHeatReporter

/-! One original funded hierarchy for every finite quiet winding order.
The native activated degree diverges along the selected course, so no
early, low-grade station pays an infinite family of gear charges. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetFiniteHeatHierarchy
open Function Filter Finset Lattice Wilson RG WilsonCoeffUV WilsonCoeffUV.Bank
open PhysicalNext.Repeat.Legato Next.Foundations WilsonMarkedIndependentPhysicalIntake
open WilsonVacuumPreResetFiniteHeatScale WilsonVacuumPreResetFiniteHeatTable
open scoped Topology BigOperators Classical

/-- Both the full unaliased finite table and its rooted positive-angular
receipt on a single Wilson history at every fixed comparison order. -/
theorem original (G:Gauge):∃v:ℕ→Gear G→ℝ,∀(R:Run G),G.Simple→
    RG05Preconstruction.ReadoutPurchase R.b→FundedMarkedCoverRows.prices v R.kit→
    ∀e:ℕ,∀ᶠm:ℕ in atTop,∃s B:ℝ,0<s ∧ 1 ≤ B ∧ ∀N p:ℕ,m ≤ N→
      table R.family.path.levels R.metals.O e N m (R.family.side m p) (rate R.family.path.levels m p) ∧
      PositiveAt R.family.path.levels R.metals.O e N m (R.family.side m p) s B:=by
  classical
  choose u step using WilsonVacuumPreResetFiniteHeatStep.original G
  let v(j:ℕ)(I:Gear G):ℝ:=∑o∈range (j+1),|u o j I|
  have domination (j e:ℕ)(he:e ≤ j)(I:Gear G):u e j I ≤ v j I:=
    (le_abs_self _).trans (Finset.single_le_sum (f:=fun o=>|u o j I|)
      (fun o _=>abs_nonneg _) (mem_range.mpr (by omega)))
  refine ⟨v,?_⟩
  intro R simple reading paid e
  let L:=R.family.path.levels
  have grows:Tendsto (fun k:ℕ=>L.clock.J (k+1)) atTop atTop:=L.fits.deep.comp (tendsto_add_atTop_nat 1)
  obtain ⟨grade,large⟩:=eventually_atTop.mp (grows.eventually_ge_atTop e)
  obtain ⟨start,stages⟩:=eventually_atTop.mp (step e R simple reading)
  obtain ⟨first,estate⟩:=eventually_atTop.mp (FundedMarkedCoverRows.realm R simple v paid 0 (fun _=>0)
    (fun _=>1) (fun _=>by decide) e 0 0)
  filter_upwards [eventually_ge_atTop (max (max grade start) (first+1))] with m hm
  let b:=m-1
  have date:b+1=m:=by dsimp [b];omega
  have hb:b ≤ m:=by omega
  obtain ⟨Q,draws,O,clock,anchor,_,_,_,book⟩:=estate b (by dsimp [b];omega)
  have raw(N p:ℕ)(live:m ≤ N):
      table L R.metals.O e N m (R.family.side m p) (rate L m p):=by
    have down(k:ℕ):∀j,m ≤ j→j+k=N→
        table L R.metals.O e N j (R.family.side j p) (rate L j p):=by
      induction k with
      | zero =>
        intro j _ tag
        have eqj:j=N:=by omega
        subst j
        exact WilsonVacuumPreResetFiniteHeatTable.top R e N (R.family.side N p) (Real.exp_pos _).le
      | succ k ih =>
        intro j hj tag
        have here:Q.anchor ≤ j:=anchor ▸ hb.trans hj
        obtain ⟨_,_,cash⟩:=book j (hb.trans hj) here
        have tariff:=(domination (L.clock.J (j+1)) e (large j (by omega)) (Q.mint j here).gear).trans cash
        exact stages j (by omega) Q here draws O clock tariff N p (by omega) (ih (j+1) (by omega) (by omega))
    exact down (N-m) m le_rfl (by omega)
  have filed:=WilsonVacuumPreResetFiniteHeatSpatial.filed R Q draws O clock b anchor.le (by
    rw [date]; exact raw)
  rw [date] at filed
  obtain ⟨s,B,positive,one,spatial⟩:=filed
  exact ⟨s,B,positive,one,fun N p hN=>⟨raw N p hN,spatial N p hN⟩⟩

end YM.Integration.WilsonVacuumPreResetFiniteHeatHierarchy
