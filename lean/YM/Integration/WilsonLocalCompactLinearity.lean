import YM.Integration.WilsonLocalCompactCenteredSegment

/-! Exact linearity of the two normalized positive kernels on bounded
measurable observables, without any gauge condition on an intermediate sum. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonLocalCompactLinearity
open Filter Finset MeasureTheory Lattice RG Wilson Tree RG16 Precision PertExtension OPE OPE.Log Trace.Pilot
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato OPE.Therm Pert.Asymptotics
open PhysicalNext.Repeat.Daisy.Charity.RG12 OriginalMarkedRunAction
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open WilsonReportingForestPivots WilsonLocalCompactTransition
open scoped Classical Topology
variable {X Y Z:Type} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

structure Laws (K:(X→ℝ)→Y→ℝ):Prop where
  envelope:∀f,Envelope f→Envelope (K f)
  mix:∀f h,Envelope f→Envelope h→∀a:ℝ,K (fun x=>f x+a*h x)=fun y=>K f y+a*K h y
  constant:∀a:ℝ,K (fun _=>a)=fun _=>a

theorem identity:Laws (X:=X) (Y:=X) id:=⟨fun _ h=>h,fun _ _ _ _ _=>rfl,fun _=>rfl⟩

theorem after {K:(X→ℝ)→Y→ℝ} {M:(Y→ℝ)→Z→ℝ} (hK:Laws K) (hM:Laws M):Laws (fun F=>M (K F)):=by
  refine ⟨fun f e=>hM.envelope _ (hK.envelope f e),?_,?_⟩
  · intro f h ef eh a
    rw [hK.mix f h ef eh a,hM.mix _ _ (hK.envelope _ ef) (hK.envelope _ eh)]
  · intro a;rw [hK.constant a,hM.constant a]

private theorem weighted {μ:Measure X} {ρ f:X→ℝ} (cash:Integrable ρ μ) (ef:Envelope f):
    Integrable (fun x=>ρ x*f x) μ:=
  (cash.norm.mul_const ef.cost.choose).mono' (cash.aestronglyMeasurable.mul ef.meas.aestronglyMeasurable)
    (Eventually.of_forall fun x=>by
      rw [norm_mul];exact mul_le_mul_of_nonneg_left (ef.cost.choose_spec x) (norm_nonneg _))

theorem mix {μ:Measure X} {ρ f h:X→ℝ} (cash:Integrable ρ μ) (ef:Envelope f) (eh:Envelope h) (a:ℝ):
    (∫x,ρ x*(f x+a*h x) ∂μ)=(∫x,ρ x*f x ∂μ)+a*(∫x,ρ x*h x ∂μ):=by
  simp only [mul_add,show ∀x,ρ x*(a*h x)=a*(ρ x*h x) from fun x=>by ring,
    integral_add (weighted cash ef) ((weighted cash eh).const_mul a),integral_const_mul]

variable {G:Gauge} {I:Type} [Fintype I]

theorem physical (C:Family G) (makes:C.Makes) {N per i:ℕ} (live:i<N):
    Laws (actualAverage C (N:=N) (p:=per) (m:=i) (E:=ℝ)):=by
  refine ⟨?_,?_,fun a=>funext (actualAverage_const C makes live a)⟩
  · intro f ef
    have report:=WilsonCoherentEarlier.envelope C makes (Nat.succ_le_of_lt live) ef (Nat.le_succ i)
    rw [actualTransport_step C makes (Nat.succ_le_of_lt live) f (Nat.lt_succ_self i),actualTransport_base C makes (Nat.succ_le_of_lt live)] at report
    exact report
  · intro f h ef eh a;funext V
    simpa only [actualAverage,smul_eq_mul] using mix (actualConditionalDensity_integrable C makes live V) ef eh a

theorem transported (C:Family G) (makes:C.Makes) {N per l:ℕ} (cut:l≤N) {j:ℕ} (live:j≤l):
    Laws (fun H:Config G (C.side l per)→ℝ=>actualTransport C (N:=N) H live):=by
  induction live using Nat.decreasingInduction with
  | self=>
    simp only [actualTransport_base C makes cut]
    exact ⟨fun _ h=>h,fun _ _ _ _ _=>rfl,fun _=>rfl⟩
  | of_succ i hi ih=>
    simpa only [actualTransport_step C makes cut _ hi] using after ih (physical C makes (per:=per) (hi.trans_le cut))

theorem funded (R:Run G) (simple:G.Simple)
    (marks:Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay)
    (fees:Mallow.RG12.Earned (GapsLocal.Renew.checkout G) R.kit.shape R.alloy.delay)
    (slow:∀m,((R.family.S.block m).val:ℝ)≤Real.log (Lambda R.family.path.levels m))
    (d:I→ℕ) (grade:ℕ) (ord:5≤grade):
    ∀ᶠm:ℕ in atTop,∀N (live:m+1<N) per (o:I→Site (R.family.side (m+1) per))
      (T:Forest (R.family.path.levels.clock.op m per).ratio),
      Laws (send R live grade T (incident R T d o)):=by
  filter_upwards [WilsonLocalCompactPosterior.original R simple marks fees slow d 0 grade ord zero_lt_one,
    WilsonLocalCompactTransition.original R simple marks fees slow d 0 grade ord zero_lt_one] with i paid program N live per o T
  let B:=incident R T d o
  have unit (V):=paid N live per o T V (fun _=>1) (Envelope.const 1) (fun _ _=>rfl)
  have pull (f:Config G (R.family.side (i+1) per)→ℝ) (e:Envelope f):
      Envelope (fun u:T.Slice G=>f (T.drape u)):=⟨e.meas.comp T.continuous_drape.measurable,e.cost.choose,fun u=>e.cost.choose_spec _⟩
  refine ⟨(program N live per o T).1,?_,?_⟩
  · intro f h ef eh a;funext V
    have total:=mix (unit V).1 (pull f ef) (pull h eh) a
    dsimp only [send]
    rw [total];ring
  · intro a;funext V;dsimp only [send]
    rw [integral_mul_const]
    field_simp [(unit V).2.2.1.ne']

end YM.Integration.WilsonLocalCompactLinearity
