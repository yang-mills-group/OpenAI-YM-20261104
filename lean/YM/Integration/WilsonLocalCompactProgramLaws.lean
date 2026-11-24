import YM.Integration.WilsonLocalCompactLinearity

/-! Every finite composition on an admitted interval preserves bounded
observables, real linear combinations and each physical constant exactly. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonLocalCompactProgramLaws
open Filter Finset MeasureTheory Lattice RG Wilson Tree RG16 Precision PertExtension OPE OPE.Log Trace.Pilot
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato OPE.Therm Pert.Asymptotics
open PhysicalNext.Repeat.Daisy.Charity.RG12 OriginalMarkedRunAction
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open WilsonReportingForestPivots WilsonLocalCompactHistory WilsonLocalCompactLinearity
open scoped Classical Topology
variable {G:Gauge} {I:Type} [Fintype I] (R:Run G)

theorem original (simple:G.Simple)
    (marks:Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay)
    (fees:Mallow.RG12.Earned (GapsLocal.Renew.checkout G) R.kit.shape R.alloy.delay)
    (slow:∀m,((R.family.S.block m).val:ℝ)≤Real.log (Lambda R.family.path.levels m))
    (d:I→ℕ) (grade:ℕ) (ord:5≤grade):
    ∀ᶠj:ℕ in atTop,∀l (live:j≤l) N (interior:l<N) per
       (T:∀i,i<l→Forest (R.family.path.levels.clock.op i per).ratio)
       (o:∀i,i<l→I→Site (R.family.side (i+1) per)),
      Laws (fun H=>program R interior grade d T o H live):=by
  obtain ⟨s,bank⟩:=eventually_atTop.1 (funded R simple marks fees slow d grade ord)
  refine eventually_atTop.2 ⟨s,?_⟩
  intro j sj l live N interior per T o
  induction live using Nat.decreasingInduction with
  | self=>
    simp only [start]
    exact ⟨fun _ e=>e,fun _ _ _ _ _=>rfl,fun _=>rfl⟩
  | of_succ i hi ih=>
    have previous:=ih (sj.trans (Nat.le_succ i))
    have next:=bank i sj N ((Nat.succ_le_of_lt hi).trans_lt interior) per (o i hi) (T i hi)
    simpa only [step R interior grade d T o _ hi] using after previous next

end YM.Integration.WilsonLocalCompactProgramLaws
