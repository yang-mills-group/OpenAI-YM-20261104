import YM.Integration.WilsonReportingForestRelative

/-! The full original conditional on all occupied internal free links. The
other forest links participate through the same exterior variable v, with
all signed insertions retained in the original Gibbs density. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonReportingForestPivots
open Function Filter Finset Set MeasureTheory Metric Lattice RG Wilson Tree Precision PertExtension
open PhysicalNext.Repeat.Legato MSbar.Heath OPE.Therm RG16 WilsonPhysicalRegisteredForestAction
open scoped Classical Topology
variable {G:Gauge} (R:Run G) {I:Type} [Fintype I]
local notation "A"=>R.family.path

omit R [Fintype I] in
private theorem scatter {c f:Side} {S:StepData c f} (T:Forest S.ratio) (E:Finset T.Free)
    (event:Config G f→ℝ) (ee:Envelope event)
    (change:∀(g:Site f→G.El), (∀i,g (S.ratio.embed i)=1) → ∀U,event (Lattice.gauge g U)=event U):
    (∫U,event U ∂prior G f)=∫v:({e:T.Free|e∉E}:Set T.Free)→G.El,
      (∫x,event (filled T E v x) ∂Chart.physical G (↥E)) ∂Measure.pi (fun _=>G.probHaar) := by
  have et:Envelope (fun u:T.Slice G=>event (T.drape u)):=
    ⟨ee.meas.comp T.continuous_drape.measurable,ee.cost.choose,fun u=>ee.cost.choose_spec (T.drape u)⟩
  letI : IsProbabilityMeasure (T.order G):=inferInstanceAs (IsProbabilityMeasure (Measure.pi fun _:T.Free=>G.probHaar))
  have ms : MeasurePreserving (cut T E) (T.order G)
      ((Chart.physical G (↥E)).prod (Measure.pi fun _ : ({e : T.Free | e∉E}:Set T.Free)=>G.probHaar)) := by
    convert! measurePreserving_piEquivPiSubtypeProd (α:=fun _:T.Free=>G.El) (fun _=>G.probHaar) (·∈E) using 1
    unfold Chart.physical;congr;apply Subsingleton.elim
  letI : IsProbabilityMeasure (Chart.physical G (↥E)) := by unfold Chart.physical;infer_instance
  letI : SFinite (Chart.physical G (↥E)) := by unfold Chart.physical;infer_instance
  have it:=ms.symm.integrable_comp_of_integrable (et.integrable (T.order G))
  rw [T.pack event (ee.integrable _) change,← ms.symm.integral_comp']
  have fibers:=integral_prod_symm (μ:=Chart.physical G (↥E)) (ν:=Measure.pi fun _:({e:T.Free|e∉E}:Set T.Free)=>G.probHaar) _ it
  simp only [Function.comp_apply] at fibers
  exact fibers

/-- On every held lower field the original normalized nonlinear integral
uses one Lie ball for all altered internal and crossing coordinates,
with one genuine exterior pivot for each ordered pair of parents. -/
theorem original (simple:G.Simple) (slow:∀m,((R.family.S.block m).val:ℝ)≤Real.log (Lambda (A).levels m))
    (J:Voice G) (clear:Clear G J) (P:ChartRatio G) (hp:LocalRatio P) {r:ℝ} (pr:0<r) (sr:r<Chart.small G P) (d:I→ℕ) :
    ∀ᶠ m:ℕ in atTop,∀N,m<N→∀per (o:I→Site (R.family.side (m+1) per)) (T:Forest ((A).levels.clock.op m per).ratio)
    (V:Config G (R.family.side m per)) (H:Config G (R.family.side (m+1) per)→ℝ),Envelope H→GaugeInvariant H→
    let B:=incident R T d o
    let E:=moving T B
    let C:=cold R m per d o
    let w:=actualConditionalDensity R.family N per m V
    actualAverage R.family (N:=N) (C.indicator H) V=
      ∫v:({i:T.Free|i∉E}:Set T.Free)→G.El,
        (∫x in ball 0 r,Chart.jacobian P x * C.indicator (fun U=>w U*H U)
          (restored T B v (Chart.expLinks G (↥E) x)) ∂Chart.tangent G (↥E)) ∂Measure.pi (fun _=>G.probHaar) := by
  filter_upwards [relative R simple slow J clear P hp pr sr d] with m ruled N live per o T V H eh inv
  dsimp only
  let S:=(A).levels.clock.op m per
  let B:=incident R T d o
  let E:=moving T B
  let C:=cold R m per d o
  let w:=actualConditionalDensity R.family N per m V
  let event:=C.indicator (fun U=>w U*H U)
  have mc:MeasurableSet C:=MeasurableSet.iInter (fun _=>House.bath _)
  obtain ⟨c,hc,lo⟩:=WilsonHeldExteriorLaw.upper_floor R N per m live
  have ew:Envelope w := (WilsonHeldExteriorLaw.regularity R N per m live V ((A).rep N per (m+1))
    (((A).rep N per (m+1)).envelope (R.makes.wilson.represents N per (m+1) live).good) hc lo).1
  have ee:Envelope event:=Envelope.piece mc (ew.mul eh) (Envelope.const 0)
  have change (g : Site (R.family.side (m+1) per)→G.El) (pins : ∀i,g ((S).ratio.embed i)=1) (U:Config G (R.family.side (m+1) per)) : event (Lattice.gauge g U)=event U := by
    have c : Lattice.gauge (g ∘ (S).ratio.embed) V=V:=by funext e;simp [Lattice.gauge,Function.comp,pins]
    have w0:=WilsonPhysicalRegisteredLocalAction.covariant A R.makes.wilson live g U V
    rw [c] at w0
    have wf (u:Config G (R.family.side (m+1) per)):w u=WilsonPhysicalRegisteredLocalAction.weight A N per m u V:=by
      unfold w actualConditionalDensity WilsonPhysicalRegisteredLocalAction.weight;rw [mul_comm ((S).density ..)]
    have cg : Lattice.gauge g U∈C ↔ U∈C:=by simp only [C,cold,Set.mem_iInter,House.chilly,Set.mem_setOf_eq,face_gauge,G.chord_conj]
    unfold event;by_cases hu:U∈C
    · rw [Set.indicator_of_mem (cg.mpr hu),Set.indicator_of_mem hu,wf,wf,w0,inv g U]
    · rw [Set.indicator_of_notMem (fun h=>hu (cg.mp h)),Set.indicator_of_notMem hu]
  have start:actualAverage R.family (N:=N) (C.indicator H) V=∫U,event U ∂prior G _:=by
    apply integral_congr_ae;apply ae_of_all;intro U;by_cases h:U∈C <;> simp [event,h,w,smul_eq_mul]
  rw [start,scatter T E event ee change]
  apply integral_congr_ae;apply ae_of_all;intro v
  exact ruled per o T v (fun U=>w U*H U) (ew.meas.mul eh.meas)

end YM.Integration.WilsonReportingForestPivots
