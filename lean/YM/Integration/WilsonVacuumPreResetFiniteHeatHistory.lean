import YM.Integration.WilsonVacuumPreResetFiniteHeatStep

/-! The true finite quiet program and the independent folded quiet program
on the selected Wilson course, uniformly before every UV top and period. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonVacuumPreResetFiniteHeatHistory
open Filter Finset Lattice Wilson RG WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket
open PhysicalNext.Repeat.Legato Next.Foundations
open WilsonVacuumPreResetFiniteHeatScale WilsonVacuumPreResetFiniteHeatTable
open scoped Topology
variable {G:Gauge}

/-- One finite pre-election quote buys the full backward history for every
original period. The upper cutoff is selected after the reporting mesh. -/
theorem original (G:Gauge)(e:ℕ):∃v:ℕ→Gear G→ℝ,∀(R:Run G),G.Simple→
    RG05Preconstruction.ReadoutPurchase R.b→FundedMarkedCoverRows.prices v R.kit→
    ∀ᶠ m:ℕ in atTop,∀N p:ℕ,m ≤ N→
      table R.family.path.levels R.metals.O e N m (R.family.side m p) (rate R.family.path.levels m p):=by
  obtain ⟨v,row⟩:=WilsonVacuumPreResetFiniteHeatStep.original G e
  refine ⟨v,?_⟩
  intro R simple reading funding
  obtain ⟨m₀,available⟩:=eventually_atTop.mp (row R simple reading)
  have prior:=FundedMarkedCoverRows.realm R simple v funding 0 (fun _=>0) (fun _=>1)
    (fun _=>by decide) e 0 0
  filter_upwards [eventually_ge_atTop m₀,prior] with m hm hQ N p live
  obtain ⟨Q,draws,O,clock,anchor,_,_,_,budget⟩:=hQ
  have descend (k:ℕ):∀j,m ≤ j→j+k=N→
      table R.family.path.levels R.metals.O e N j (R.family.side j p) (rate R.family.path.levels j p):=by
    induction k with
    | zero =>
      intro j _ hj
      have eqj:j=N:=by omega
      subst j
      exact WilsonVacuumPreResetFiniteHeatTable.top R e N (R.family.side N p) (Real.exp_pos _).le
    | succ k ih =>
      intro j hj atN
      have hQj:Q.anchor ≤ j:=anchor ▸ hj
      obtain ⟨_,_,paid⟩:=budget j hj hQj
      exact available j (hm.trans hj) Q hQj draws O clock paid N p (by omega)
        (ih (j+1) (by omega) (by omega))
  exact descend (N-m) m le_rfl (by omega)

end YM.Integration.WilsonVacuumPreResetFiniteHeatHistory
