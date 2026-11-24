import YM.Integration.WilsonLocalCompactTransition
import YM.Integration.WilsonLocalCompactHistoryGauge

/-! Compose the actual normalized compact retained kernels at successive
reporting dates. Positivity charges each approximation once in the entire
finite Wilson history. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonLocalCompactHistory
open Function Filter Set Finset MeasureTheory Lattice RG Wilson Tree RG16 Precision PertExtension
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato OPE.Therm Pert.Asymptotics
open PhysicalNext.Repeat.Daisy.Charity.RG12 OriginalMarkedRunAction
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open WilsonReportingForestPivots WilsonLocalCompactTransition
open scoped Classical Topology BigOperators
variable {G:Gauge} {I:Type} [Fintype I] (R:Run G) {N per b:ℕ}
local notation "Space" => fun i=>Config G (R.family.side i per)

def program (top:b<N) (grade:ℕ) (d:I→ℕ) (T:∀i,i<b→Forest (R.family.path.levels.clock.op i per).ratio)
    (o:∀i,i<b→I→Site (R.family.side (i+1) per)) (H:Space b→ℝ) {j:ℕ} (live:j≤b):Space j→ℝ:=
  Nat.decreasingInduction (motive:=fun i _=>Space i→ℝ)
    (fun i hi=>send R ((Nat.succ_le_of_lt hi).trans_lt top) grade (T i hi) (incident R (T i hi) d (o i hi))) H live

theorem start (top:b<N) (grade:ℕ) (d:I→ℕ) (T:∀i,i<b→Forest (R.family.path.levels.clock.op i per).ratio)
    (o:∀i,i<b→I→Site (R.family.side (i+1) per)) (H:Space b→ℝ):
    program R top grade d T o H le_rfl=H:=Nat.decreasingInduction_self ..

theorem step (top:b<N) (grade:ℕ) (d:I→ℕ) (T:∀i,i<b→Forest (R.family.path.levels.clock.op i per).ratio)
    (o:∀i,i<b→I→Site (R.family.side (i+1) per)) (H:Space b→ℝ) {i:ℕ} (hi:i<b):
    program R top grade d T o H hi.le=
      send R ((Nat.succ_le_of_lt hi).trans_lt top) grade (T i hi) (incident R (T i hi) d (o i hi)) (program R top grade d T o H hi):=Nat.decreasingInduction_succ_left ..

theorem original (simple:G.Simple)
    (marks:Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay)
    (fees:Mallow.RG12.Earned (GapsLocal.Renew.checkout G) R.kit.shape R.alloy.delay)
    (slow:∀m,((R.family.S.block m).val:ℝ)≤Real.log (Lambda R.family.path.levels m))
    (d:I→ℕ) (q grade:ℕ) (ord:q+5≤grade) {ε:ℝ} (ep:0<ε):
    ∀ᶠj:ℕ in atTop,∀b (live:j≤b) N (top:b<N) per
      (T:∀i,i<b→Forest (R.family.path.levels.clock.op i per).ratio)
      (o:∀i,i<b→I→Site (R.family.side (i+1) per))
      (H:Config G (R.family.side b per)→ℝ),Envelope H→GaugeInvariant H→
    ∀C:ℝ,(∀U,|H U|≤C)→
    let v:=program R top grade d T o H live
    let F:=actualTransport R.family (N:=N) H live
    let δ:=fun i=>ε*regulatorRun R.family N per (i+1)^q
    Envelope v ∧ ∀V,|v V-F V|≤∑i∈Ico j b,2*(δ i*(1+δ i))*C:=by
  obtain ⟨k,bank⟩:=eventually_atTop.1 (WilsonLocalCompactTransition.original R simple marks fees slow d q grade ord ep)
  filter_upwards [Ici_mem_atTop k] with j hj b live N top per T o H eh gh C bound
  let δ:=fun i=>ε*regulatorRun R.family N per (i+1)^q
  let cost:=fun i=>2*(δ i*(1+δ i))*C
  change Envelope (program R top grade d T o H live) ∧
    ∀V,|program R top grade d T o H live V-actualTransport R.family (N:=N) H live V|≤∑i∈Ico j b,cost i
  induction live using Nat.decreasingInduction with
  | self=>
    rw [start,actualTransport_base R.family R.makes top.le]
    exact ⟨eh,fun _=>by simp⟩
  | of_succ i hi ih=>
    have oldk : k ≤ i := hj
    have later : k ≤ i+1 := oldk.trans (Nat.le_succ i)
    have prior:=ih later
    let f:=actualTransport R.family (N:=N) H (Nat.succ_le_of_lt hi)
    let v:=program R top grade d T o H (Nat.succ_le_of_lt hi)
    let K:=send R ((Nat.succ_le_of_lt hi).trans_lt top) grade (T i hi) (incident R (T i hi) d (o i hi))
    have monge:Funded R N per i K (δ i):=bank i hj N ((Nat.succ_le_of_lt hi).trans_lt top) per (o i hi) (T i hi)
    have real:=WilsonLocalCompactHistoryGauge.original R.family R.makes top.le (Nat.succ_le_of_lt hi) H eh gh
    have old (U):|f U|≤C:=by
      simpa only [Real.norm_eq_abs] using actualTransport_norm_le R.family R.makes top.le (I:=H) (fun U=>by simpa only [Real.norm_eq_abs] using bound U) (Nat.succ_le_of_lt hi) U
    have first:=monge.2.1 v f prior.1 real.1 (∑i∈Ico (i+1) b,cost i) prior.2
    have second:=monge.2.2 f real.1 real.2 C old
    rw [step R top grade d T o H hi,actualTransport_step R.family R.makes top.le H hi]
    refine ⟨monge.1 v prior.1,fun V=>?_⟩
    calc |K v V-actualAverage R.family (N:=N) f V|
        ≤ |K v V-K f V|+|K f V-actualAverage R.family (N:=N) f V|:=abs_sub_le ..
      _ ≤ (∑i∈Ico (i+1) b,cost i)+cost i:=add_le_add (first V) (second V)
      _ = ∑l∈Ico i b,cost l:=by rw [add_comm,Finset.sum_eq_sum_Ico_succ_bot hi cost]

end YM.Integration.WilsonLocalCompactHistory
