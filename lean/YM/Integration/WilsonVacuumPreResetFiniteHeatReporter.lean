import YM.Integration.WilsonVacuumPreResetFiniteHeatSpatial

/-! The original positive quiet receipt needed by the received marked
history, at the enrolled side and before every physical cutoff and period. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetFiniteHeatReporter
open Function Filter Lattice RG Wilson WilsonCoeffUV WilsonCoeffUV.Bank
open PhysicalNext.Repeat.Legato Next.Foundations WilsonMarkedIndependentPhysicalIntake
open scoped Topology
variable {G:Gauge} {e:ℕ}

theorem original (G:Gauge)(e:ℕ):∃v:ℕ→Gear G→ℝ,∀(R:Run G),G.Simple→
    RG05Preconstruction.ReadoutPurchase R.b→FundedMarkedCoverRows.prices v R.kit→
    ∀ᶠm:ℕ in atTop,∃s B:ℝ,0<s ∧ 1 ≤ B ∧ ∀N p:ℕ,m ≤ N→
      PositiveAt R.family.path.levels R.metals.O e N m (R.family.side m p) s B:=by
  obtain ⟨v,all_dates⟩:=WilsonVacuumPreResetFiniteHeatHistory.original G e
  refine ⟨v,?_⟩
  intro R simple reading paid
  obtain ⟨m₀,raw⟩:=eventually_atTop.mp (all_dates R simple reading paid)
  obtain ⟨j₀,estate⟩:=eventually_atTop.mp (FundedMarkedCoverRows.realm R simple v paid 0
    (fun _=>0) (fun _=>1) (fun _=>by decide) e 0 0)
  filter_upwards [eventually_ge_atTop (max m₀ (j₀+1))] with m enrolled
  let j:=m-1
  have stage:j+1=m:=by dsimp [j];omega
  obtain ⟨Q,draws,O,clock,anchor,_⟩:=estate j (by dsimp [j];omega)
  have posted:=WilsonVacuumPreResetFiniteHeatSpatial.filed R Q draws O clock j anchor.le
    (raw (j+1) (by omega))
  simpa only [stage] using posted

end YM.Integration.WilsonVacuumPreResetFiniteHeatReporter
