import YM.Integration.WilsonLocalHeldKernelIntegral

/-! Projecting the whole held transition kernel preserves the gauge symmetry
used by the original forest before the coarse field is fixed. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonLocalHeldKernelChart
open Function Filter Set Finset MeasureTheory Metric Lattice RG Wilson Tree RG16 Precision PertExtension
open PhysicalNext.Repeat.Legato MSbar.Heath OPE.Therm Pert.Asymptotics
open WilsonReportingForestPivots WilsonPhysicalRegisteredForestAction WilsonLocalReportingChartIntegral
open scoped Classical Topology
variable {G:Gauge} {I:Type} [Fintype I] {c f:Side} {S:StepData c f}

def Pinned (S:StepData c f) (a:Config G f→ℝ) : Prop :=
  ∀g:Site f→G.El,(∀i,g (S.ratio.embed i)=1)→∀U,a (Lattice.gauge g U)=a U

def reduced (R:Run G) (N per m:ℕ) (V:Config G (R.family.side m per)) (U:Config G (R.family.side (m+1) per)) : ℝ :=
  (R.family.path.levels.clock.op m per).density (R.family.path.β N per (m+1)) U V/(R.family.path.rep N per m).eval V

theorem density (R:Run G) (N per m:ℕ) (V:Config G (R.family.side m per)) (U:Config G (R.family.side (m+1) per)) :
    actualConditionalDensity R.family N per m V U=reduced R N per m V U*(R.family.path.rep N per (m+1)).eval U := by
  unfold actualConditionalDensity reduced
  ring

theorem projected (R:Run G) (N per m:ℕ) (read:(Config G (R.family.side m per)→ℝ)→ℝ) :
    Pinned (R.family.path.levels.clock.op m per) (fun U=>read (fun V=>reduced R N per m V U)) := by
  intro g pins U
  apply congrArg read
  funext V
  have fixed:Lattice.gauge (g∘(R.family.path.levels.clock.op m per).ratio.embed) V=V:=by
    funext e;simp [Lattice.gauge,comp,pins]
  unfold reduced
  rw [show (R.family.path.levels.clock.op m per).density _ (Lattice.gauge g U) V=_ from
    fixed ▸ (R.family.path.levels.blocks m per).gauge (R.family.path.β N per (m+1)) U V g]

theorem scatter (T:Forest S.ratio) (E:Finset T.Free) (event:Config G f→ℝ) (ee:Envelope event) (saved:Pinned S event) :
    (∫U,event U ∂prior G f)=∫v:({e:T.Free|e∉E}:Set T.Free)→G.El,
       (∫x,event (filled T E v x) ∂Chart.physical G (↥E)) ∂Measure.pi (fun _=>G.probHaar) := by
  have et:Envelope (fun u:T.Slice G=>event (T.drape u)):=
    ⟨ee.meas.comp T.continuous_drape.measurable,ee.cost.choose,fun u=>ee.cost.choose_spec (T.drape u)⟩
  letI : IsProbabilityMeasure (T.order G):=inferInstanceAs (IsProbabilityMeasure (Measure.pi fun _:T.Free=>G.probHaar))
  have ms:MeasurePreserving (cut T E) (T.order G)
      ((Chart.physical G (↥E)).prod (Measure.pi fun _:({e:T.Free|e∉E}:Set T.Free)=>G.probHaar)) := by
    convert! measurePreserving_piEquivPiSubtypeProd (α:=fun _:T.Free=>G.El) (fun _=>G.probHaar) (·∈E) using 1
    unfold Chart.physical;congr;apply Subsingleton.elim
  letI : IsProbabilityMeasure (Chart.physical G (↥E)):=by unfold Chart.physical;infer_instance
  letI : SFinite (Chart.physical G (↥E)):=by unfold Chart.physical;infer_instance
  have it:=ms.symm.integrable_comp_of_integrable (et.integrable (T.order G))
  rw [T.pack event (ee.integrable _) saved,←ms.symm.integral_comp']
  exact integral_prod_symm _ it

theorem original (R:Run G) (simple:G.Simple) (slow:∀m,((R.family.S.block m).val:ℝ)≤Real.log (Lambda R.family.path.levels m))
    (J:Voice G) (clear:Clear G J) (P:ChartRatio G) (hp:LocalRatio P) {r:ℝ}
    (pr:0<r) (sr:r < Chart.small G P) (d:I→ℕ) :
    ∀ᶠm:ℕ in atTop,∀per (o:I→Site (R.family.side (m+1) per)) (T:Forest (R.family.path.levels.clock.op m per).ratio)
    (h:Config G (R.family.side (m+1) per)→ℝ), Envelope h→Pinned (R.family.path.levels.clock.op m per) h→
    let B:=incident R T d o
    let C:=cold R m per d o
    (∫U,C.indicator h U ∂prior G (R.family.side (m+1) per))=
      ∫z,entry P T B C h z ∂law G T B r := by
  filter_upwards [relative R simple slow J clear P hp pr sr d] with m angles per o T h bounded changed
  intro B C
  have ms:MeasurableSet C:=MeasurableSet.iInter (fun _=>House.bath _)
  have env:Envelope (C.indicator h):=Envelope.piece ms bounded (Envelope.const 0)
  have fixed:Pinned (R.family.path.levels.clock.op m per) (C.indicator h) := by
    intro g pins U
    have mem:Lattice.gauge g U∈C ↔ U∈C:=by simp only [C,cold,mem_iInter,House.chilly,mem_setOf_eq,face_gauge,G.chord_conj]
    by_cases live:U∈C
    · rw [indicator_of_mem (mem.mpr live),indicator_of_mem live,changed g pins U]
    · rw [indicator_of_notMem (fun hit=>live (mem.mp hit)),indicator_of_notMem live]
  calc
    _ = _ := scatter T (moving T B) _ env fixed
    _ = ∫v:({e:T.Free|e∉moving T B}:Set T.Free)→G.El,
        (∫x in ball 0 r,entry P T B C h (v,x) ∂Chart.tangent G (↥(moving T B)))
          ∂Chart.physical G ({e:T.Free|e∉moving T B}:Set T.Free) := by
      apply integral_congr_ae;apply ae_of_all;intro v
      exact angles per o T v h bounded.meas
    _ = _ := (integral_prod _ (integrable P hp T B ms bounded pr sr)).symm

end YM.Integration.WilsonLocalHeldKernelChart
