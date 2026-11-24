import YM.Integration.WilsonLocalCompactMean

/-! Positive comparison of the two genuine one-step laws in an arbitrary
transported majorant, retaining the full exterior-dependent normalizer. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonLocalCompactMajorant
open Function Set Filter MeasureTheory Lattice RG Wilson Tree RG16 Precision PertExtension
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato OPE.Therm Pert.Asymptotics
open PhysicalNext.Repeat.Daisy.Charity.RG12 OriginalMarkedRunAction
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open WilsonReportingForestPivots WilsonLocalCompactTransition WilsonLocalCompactPosteriorWeight
open scoped Classical Topology
variable {G:Gauge} {I:Type} [Fintype I] (R:Run G)

theorem original (simple:G.Simple)
    (marks:Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay)
    (fees:Mallow.RG12.Earned (GapsLocal.Renew.checkout G) R.kit.shape R.alloy.delay)
    (slow:∀m,((R.family.S.block m).val:ℝ)≤Real.log (Lambda R.family.path.levels m))
    (d:I→ℕ) (q grade:ℕ) (ord:q+5≤grade) {ε:ℝ} (ep:0<ε):
    ∀ᶠm:ℕ in atTop,∀N (live:m+1<N) per (o:I→Site (R.family.side (m+1) per))
      (T:Forest (R.family.path.levels.clock.op m per).ratio),
    let K:=send R live grade T (incident R T d o)
    let δ:=ε*regulatorRun R.family N per (m+1)^q
    (∀H,Envelope H→Envelope (K H)) ∧
    (∀h f A,Envelope h→Envelope f→Envelope A→∀c:ℝ,(∀U,|h U-f U|≤c*A U)→∀V,|K h V-K f V|≤c*K A V) ∧
    (∀f A,Envelope f→Envelope A→GaugeInvariant f→(∀U,|f U|≤A U)→∀V,
      |K f V-actualAverage R.family (N:=N) f V|≤2*(δ*(1+δ))*actualAverage R.family (N:=N) A V):=by
  have transitions:=WilsonLocalCompactTransition.original R simple marks fees slow d q grade ord ep
  have post:=WilsonLocalCompactPosterior.original R simple marks fees slow d q grade ord ep
  have weights:=WilsonLocalCompactPosteriorWeight.fields R simple marks fees slow d q grade ord ep
  filter_upwards [transitions,post,weights] with m stock law densities N live per o T
  let B:=incident R T d o
  let K:=send R live grade T B
  let δ:=ε*regulatorRun R.family N per (m+1)^q
  have raised {H:Config G (R.family.side (m+1) per)→ℝ} (e:Envelope H):Envelope (fun u:T.Slice G=>H (T.drape u)):=
    ⟨e.meas.comp T.continuous_drape.measurable,e.cost.choose,fun u=>e.cost.choose_spec (T.drape u)⟩
  refine ⟨(stock N live per o T).1,fun h f A eh ef ea c bound V=>?_,fun f A ef ea gf bound V=>?_⟩
  · let a:=amount R live grade T B V
    have unit:=law N live per o T V (fun _=>1) (Envelope.const 1) (fun _ _=>rfl)
    have nn (u):0≤a u:=by
      rw [show a u=_ from cancel R live grade T B V u]
      exact mul_nonneg (Multi.AxisShift.chosen_positive R.makes.wilson (by omega) V).le ((densities N live per o T V).2 u).2.1
    exact WilsonLocalCompactMean.variation unit.1 nn unit.2.2.1 (raised eh) (raised ef) (raised ea) (fun u=>bound (T.drape u))
  · have dp:0≤δ:=mul_nonneg ep.le (pow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) _)
    have physical:=WilsonLocalCompactMean.physical R.family R.makes live.le ef ea bound V
    have first:=(law N live per o T V f ef gf).2.2.2.2.2
    exact first.trans ((mul_le_mul_of_nonneg_left physical.2 (mul_nonneg dp (by linarith))).trans_eq (by ring))

end YM.Integration.WilsonLocalCompactMajorant
