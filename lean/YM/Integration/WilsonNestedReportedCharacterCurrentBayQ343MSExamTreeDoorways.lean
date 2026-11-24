import YM.Integration.WilsonOrdinaryNestedCourse
/-! The genuine prior raw tree tickets also guarantee every required detector
aperture through the full compact orbit, at its original root and at every
active parent of the complete physical casting. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
universe u
namespace YM.Integration.WilsonNestedReportedCharacterCurrentBayQ343MSExamTreeDoorways
open Filter Function Set Spec Extraction Table PhysicalNext.Repeat.Legato Climb
open OPE OPE.Log OPE.Orbits OPE.Orbits.Reader OPE.Nesting OPE.Nesting.Tree OPE.Nesting.Atom
open PhysMS Trace.Pilot WilsonCenteredNestedProgram WilsonCenteredNestedIntake WilsonCenteredNestedGross WilsonCenteredNestedSigned
open WilsonCenteredNestedLoggedRow WilsonOrdinaryNestedTariff WilsonCenteredNestedViewer
open scoped Classical BigOperators Topology
variable {G:Gauge} {R:Run G} {f:Extraction.Order} {S:Table R.family.book}
    {F:Final R.family f S} {L:EveryPhase.Almanac F}
    {Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin}
    {J:ℝ→PhysMS.tower S} {Y:(Bel R.family.book).Hierarchy} {A:Trace.Terrace.Arch R.family}
    {ℓ:Ultrafilter (ℕ×ℕ)} {simple:G.Simple} {cohort:Ultrafilter (ℕ×ℕ)→Prop}

open OPE OPE.Orbits OPE.Arboreal OPE.Arboreal.Mountain
private theorem moved {I:Type}[Fintype I](tree:Arboreal I){M δ:ℝ}{x:I→E4}{t:I→ℝ}(fund:tree.Convoy M δ t x)(K:Ortho):
    tree.Convoy M δ t (Ortho.move K ∘ x):=by
  have exactNorm (a b:E4):‖Ortho.move K a-Ortho.move K b‖=‖a-b‖:=by
    change ‖(Ortho.motion K) a-(Ortho.motion K) b‖=_
    rw [←map_sub,LinearIsometryEquiv.norm_map]
  refine ⟨fund.sizes,fun i=>?_,fun i j k forked=>?_⟩
  · simpa only [Function.comp_apply,exactNorm] using fund.travel i
  simpa only [Function.comp_apply,exactNorm] using fund.spread i j k forked
theorem original (run:WilsonViewerElectedHierarchy.Selected.{u} F L Q J Y A ℓ simple cohort)
    {I:Type}[Fintype I](tree:Arboreal I)(v:I→R.family.book.Token)(D:I→ℕ)(h:ℕ)(M δ:ℝ)
    (mp:0≤M)(gap:0<δ):
    ∀ᶠr:ℝ in 𝓝[>]0,∀(x:I→E4)(t:I→ℝ),t tree.root=r→tree.Convoy M δ t x→
    orbitMargin Q.port h (crop x tree.leaves) (x tree.root) ∧
    ∀a∈tree.zones,orbitMargin Q.port h (crop x (tree.kids a)) (x a):=by
  classical
  have bank:=OPE.tickets_suffice F run.facilities run.original run.matrix Q.spans
  choose cut read using fun i:↥(bands F.sector.derivatives h)=>bank.tickets tree v i.val D M δ mp gap
  filter_upwards [Filter.eventually_all.mpr read] with r paid
  intro x t stamp funding
  have genuine (i:↥(bands F.sector.derivatives h))(K:Ortho):tree.Qualified F Q.port i.val (Ortho.move K ∘ x):=
    (paid i (Ortho.move K ∘ x) t stamp (moved tree funding K) (cut i) le_rfl).lifetimes
  constructor
  · intro i live K e he
    exact (genuine ⟨i,live⟩ K).outer e he
  intro a active i live K e he
  exact (genuine ⟨i,live⟩ K).step a e active he
end YM.Integration.WilsonNestedReportedCharacterCurrentBayQ343MSExamTreeDoorways
end
