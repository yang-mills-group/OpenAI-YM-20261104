import YM.Integration.WilsonReflectedMixedTrialSumCash
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedMixedPortfolio
open Function Filter Finset Lattice RG Wilson Source Labels Extra.Histories Extra.Histories.Relay
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph PhysicalNext PhysicalNext.Repeat.Legato
open RG05Readout RG05Readout.Address RG05Readout.Records MergeProof Push.Local Motion
open WilsonReflectedFundedHearing WilsonReflectedOpticalArm WilsonMeasuredPublicEntranceGridDebit
open WilsonAddressedMixedEnrolledTrial WilsonOriginalMicroscopicGuardedReporters
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){I:Type}[Fintype I]
local notation "C" => R.family
local notation "H" => (C).path.levels.clock.hatBeta


open WilsonReflectedMixedThermalArms

open Filter Trace.Physical.GermGraph
open scoped Topology



open WilsonReflectedMixedSharpAxis (Cash)


open OPE.Therm

/-- Before any regulators, secure the same sold all-column numerical axis,
the original charged signed physical difference on every f root for ANY Y,
and the complex portfolio's sharp financial contribution. -/
theorem original (simple:G.Simple)(shop:RG05Preconstruction.ReadoutPurchase R.b)
    (wide:∀j,1≤((C).path.levels.budget j).supportExponent)(quote:Poetry (C).path.levels)
    (D target:ℕ){η:ℝ}(pos:0<η):
    ∃gate:ℕ,∀(d:Fin (D+1)){j f K N p:ℕ}(_late:gate≤j)(first:j≤f)(up:f<K)(live:K≤N)
    {old:ℕ}{ζ:ℝ}(A:(C).label d.val≃ₗ[ℂ](C).label d.val)
    (_issued:∀x,Arrived R d.val j K N p old (first.trans up.le) live ζ A x),
    Opened C d.val j p ∧
    (∀x,Arrived R d.val j K N p target (first.trans up.le) live η A x) ∧
    (∀Y o,settled R d.val j f (K-f) N p (by rw [Nat.add_sub_of_le up.le];exact live) A Y o) ∧
    ∀(ι:Type)[Fintype ι](c:ι→ℂ)(Y:ι→(C).label d.val)(B:ι→(C).label d.val≃ₗ[ℂ](C).label d.val)
      (W:ι→ℝ){orders:ι→ℕ},
      (∀i,Cash (R:=R) d.val j f K N p (orders i) first up.le live η (B i) (Y i) (W i)) →
      Cash (R:=R) d.val j f K N p target first up.le live η A (∑i,c i•Y i) (∑i,‖c i‖*W i):=by
  classical
  obtain ⟨gate,serve⟩:=WilsonMeasuredPublicEntranceGridDebit.original R simple shop wide quote D target pos
  have doors:∀ᶠj:ℕ in atTop,∀d:Fin (D+1),∀p,Opened C d.val j p:=
    Filter.eventually_all.mpr (fun d=>open_late C simple d.val)
  obtain ⟨pad,enter⟩:=eventually_atTop.mp doors
  refine ⟨max gate pad,?_⟩
  intro d j f K N p late first up live old ζ A issued
  have openAt:=enter j ((le_max_right ..).trans late) d p
  have back:f+(K-f)=K:=Nat.add_sub_of_le up.le
  have stored:f+(K-f)≤N:=back.symm ▸ live
  obtain ⟨bank,arrived,sold⟩:=serve Unit (fun _=>d) (fun _=>j) f (K-f) N p
    (fun _=>(le_max_left ..).trans late) (fun _=>first) stored (fun _=>(first.trans_lt up).trans_le live)
  have paid:∀x,Arrived R d.val j K N p target (first.trans up.le) live η (bank ()) x:=by
    intro x
    simpa only [back] using arrived () x
  have shared:=WilsonReflectedMixedIntrinsicAxis.unique R openAt.post (first.trans up.le) live issued paid
  subst A
  have all:∀Y o,settled R d.val j f (K-f) N p stored (bank ()) Y o:=
    sold () (openAt.post.trans first)
  refine ⟨openAt,paid,all,?_⟩
  intro ι _ c Y B W orders bills
  have salary:=WilsonReflectedMixedTrialSumCash.original R openAt paid c Y B W bills (paid _)
  exact ⟨paid,salary.1,all _,salary.2⟩

end YM.Integration.WilsonReflectedMixedPortfolio
end
