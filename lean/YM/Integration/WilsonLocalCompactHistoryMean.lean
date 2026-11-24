import YM.Integration.WilsonLocalCompactMajorant

/-! Absolute conditional first-moment stability of the whole finite
retained chronology. Each genuine weight is integrated at its own date. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonLocalCompactHistoryMean
open Function Filter Set Finset MeasureTheory Lattice RG Wilson Tree RG16 Precision PertExtension
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato OPE.Therm Pert.Asymptotics
open PhysicalNext.Repeat.Daisy.Charity.RG12 OriginalMarkedRunAction
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open WilsonReportingForestPivots WilsonLocalCompactTransition WilsonLocalCompactHistory
open scoped Classical Topology
variable {G:Gauge} {I:Type} [Fintype I] (R:Run G)

theorem original (simple:G.Simple)
    (marks:Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay)
    (fees:Mallow.RG12.Earned (GapsLocal.Renew.checkout G) R.kit.shape R.alloy.delay)
    (slow:∀m,((R.family.S.block m).val:ℝ)≤Real.log (Lambda R.family.path.levels m))
    (d:I→ℕ) (q grade:ℕ) (ord:q+5≤grade) {ε:ℝ} (ep:0<ε):
    ∀ᶠj:ℕ in atTop,∀b (live:j≤b) N (top:b<N) per
      (T:∀i,i<b→Forest (R.family.path.levels.clock.op i per).ratio)
      (o:∀i,i<b→I→Site (R.family.side (i+1) per))
      (H:Config G (R.family.side b per)→ℝ),Envelope H→GaugeInvariant H→
    let v:=program R top grade d T o H live
    let f:=actualTransport R.family (N:=N) H live
    let A:=actualTransport R.family (N:=N) (fun U=>|H U|) live
    let δ:=fun i=>ε*regulatorRun R.family N per (i+1)^q
    Envelope v ∧ (∀V,|f V|≤A V) ∧
      ∀V,|v V-f V|≤(Real.exp (∑i∈Ico j b,2*(δ i*(1+δ i)))-1)*A V:=by
  obtain ⟨k,bank⟩:=eventually_atTop.1 (WilsonLocalCompactMajorant.original R simple marks fees slow d q grade ord ep)
  filter_upwards [Ici_mem_atTop k] with j hj b live N top per T o H eh gh
  let J:=fun U=>|H U|
  have ej:Envelope J:=⟨eh.meas.abs,eh.cost.choose,fun U=>by simpa only [J,Real.norm_eq_abs,abs_abs] using eh.cost.choose_spec U⟩
  have gj:GaugeInvariant J:=fun t U=>congrArg abs (gh t U)
  let δ:=fun i=>ε*regulatorRun R.family N per (i+1)^q
  let D:=fun i=>2*(δ i*(1+δ i))
  have Dp (i):0≤D i:=by
    have paid:0≤δ i:=mul_nonneg ep.le (pow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) _)
    dsimp only [D];positivity
  change Envelope (program R top grade d T o H live) ∧
    (∀V,|actualTransport R.family (N:=N) H live V|≤actualTransport R.family (N:=N) J live V) ∧
    ∀V,|program R top grade d T o H live V-actualTransport R.family (N:=N) H live V|≤
      (Real.exp (∑i∈Ico j b,D i)-1)*actualTransport R.family (N:=N) J live V
  induction live using Nat.decreasingInduction with
  | self=>
    rw [start,actualTransport_base R.family R.makes top.le,actualTransport_base R.family R.makes top.le]
    exact ⟨eh,fun _=>le_rfl,fun _=>by simp⟩
  | of_succ i hi ih=>
    have oldk : k ≤ i := hj
    have prior:=ih (oldk.trans (Nat.le_succ i))
    let f:=actualTransport R.family (N:=N) H (Nat.succ_le_of_lt hi)
    let A:=actualTransport R.family (N:=N) J (Nat.succ_le_of_lt hi)
    let v:=program R top grade d T o H (Nat.succ_le_of_lt hi)
    let K:=send R ((Nat.succ_le_of_lt hi).trans_lt top) grade (T i hi) (incident R (T i hi) d (o i hi))
    let S:=∑l∈Ico (i+1) b,D l
    have sp:0≤S:=sum_nonneg (fun l _=>Dp l)
    have xp:0≤Real.exp S-1:=sub_nonneg.mpr (Real.one_le_exp sp)
    have advance:=bank i oldk N ((Nat.succ_le_of_lt hi).trans_lt top) per (o i hi) (T i hi)
    have real:=WilsonLocalCompactHistoryGauge.original R.family R.makes top.le (Nat.succ_le_of_lt hi) H eh gh
    have full:=WilsonLocalCompactHistoryGauge.original R.family R.makes top.le (Nat.succ_le_of_lt hi) J ej gj
    have ap (U):0≤A U:=(abs_nonneg _).trans (prior.2.1 U)
    have first:=advance.2.1 v f A prior.1 real.1 full.1 (Real.exp S-1) prior.2.2
    have second:=advance.2.2 f A real.1 full.1 real.2 prior.2.1
    have third:=advance.2.2 A A full.1 full.1 full.2 (fun U=>(abs_of_nonneg (ap U)).le)
    have join:(∑l∈Ico i b,D l)=D i+S:=Finset.sum_eq_sum_Ico_succ_bot hi D
    have bill:(Real.exp S-1)*(1+D i)+D i≤Real.exp (D i+S)-1:=by
      have receipt:1+D i≤Real.exp (D i):=by linarith only [Real.add_one_le_exp (D i)]
      rw [Real.exp_add]
      nlinarith only [mul_le_mul_of_nonneg_right receipt (Real.exp_pos S).le]
    rw [step R top grade d T o H hi,actualTransport_step R.family R.makes top.le H hi,actualTransport_step R.family R.makes top.le J hi]
    have tested:=fun V=>WilsonLocalCompactMean.physical R.family R.makes (hi.trans top) real.1 full.1 prior.2.1 V
    refine ⟨advance.1 v prior.1,fun V=>(tested V).1,fun V=>?_⟩
    let y:=actualAverage R.family (N:=N) f V
    let a:=actualAverage R.family (N:=N) A V
    have pos:0≤a:=(abs_nonneg _).trans (tested V).1
    have raised:K A V≤(1+D i)*a:=by
      have low:K A V-a≤D i*a:=(le_abs_self _).trans (third V)
      linarith only [low]
    calc |K v V-y|≤|K v V-K f V|+|K f V-y|:=abs_sub_le ..
      _≤(Real.exp S-1)*K A V+D i*a:=add_le_add (first V) (second V)
      _≤(Real.exp S-1)*((1+D i)*a)+D i*a:=add_le_add (mul_le_mul_of_nonneg_left raised xp) le_rfl
      _=((Real.exp S-1)*(1+D i)+D i)*a:=by ring
      _≤(Real.exp (D i+S)-1)*a:=mul_le_mul_of_nonneg_right bill pos
      _=(Real.exp (∑l∈Ico i b,D l)-1)*a:=by rw [join]

end YM.Integration.WilsonLocalCompactHistoryMean
