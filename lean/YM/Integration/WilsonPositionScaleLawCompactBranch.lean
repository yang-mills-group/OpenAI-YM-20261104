import YM.Integration.WilsonPositionScaleLawBranch
import YM.Integration.WilsonPositionScaleLawCompactNative
import YM.Integration.WilsonPhysicalPositionDirectedTest

/-! A single directed scalar observation at half to one gives the branch on every positive compact window, including the actual calibrated fields. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawCompactBranch
open Function Filter Set Spec Table Extraction OPE OPE.Orbits Climb Trace.Pilot PhysMS Maxwell Maxwell.Free
open XSpace XSpace.Normalize
open WilsonPositionScaleLawWindow (RangeSpec Ratio sweep)
open WilsonPositionScaleLawHome (positioned)
open WilsonPositionScaleLawCompactNative
open private correct inverted from YM.Integration.WilsonPositionScaleLawBranch
open WilsonPhysicalPositionUniformBranches (change)
open private expose from YM.Integration.WilsonPhysicalPositionCocycleNative
open private engine from YM.Integration.WilsonPhysicalPositionBornTransition
open scoped Topology Classical
variable [Win:RangeSpec] {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
    (F:Final C f S)(J:ℝ→tower S)(V:Store G)
set_option quotPrecheck false
local notation "E" => (Bel C.book).Field

def Raw (d:ℕ):Prop:=Tendsto (fun z:ℝ×Ratio=>change J d z.1 z.2.val (positive z.2)) sweep
    (𝓝 (ContinuousLinearMap.id ℂ (E d)))

private theorem act {d:ℕ}(z:ℝ×Ratio)(v:E d):exactOp F J V d z v=
    Pert.Scale.gear C.labels d z.2.val⁻¹ ((WilsonPositionPrescribedFrame.change F J V d z.1).symm
      (Pert.Scale.gear C.labels d z.2.val (change J d z.1 z.2.val (positive z.2)
        (WilsonPositionPrescribedFrame.change F J V d (z.2.val*z.1) v)))):=by
  rw [show exactOp F J V d z v=_ from expose (positioned F J V) (positive z.2) v]
  apply congrArg (Pert.Scale.gear C.labels d z.2.val⁻¹)
  let A:=WilsonPositionPrescribedFrame.change F J V d
  let t:=z.2.val
  let r:=z.1
  let w:=A (t*r) v
  change (A r).symm ((J r d).symm (J (t*r) d w))=(A r).symm
    (Pert.Scale.gear C.labels d t (Frame.cocycle d J r t (positive z.2) w))
  rw [←Frame.cocycle_value d J w t r (positive z.2),(J r d).symm_apply_apply]

theorem transferred (lead:Leading F J)(d:ℕ)(raw:Raw J d):
    Tendsto (exactOp F J V d) sweep (𝓝 (ContinuousLinearMap.id ℂ (E d))):=by
  let X:=E d
  let I:=ContinuousLinearMap.id ℂ X
  let A(r:ℝ):= (WilsonPositionPrescribedFrame.change F J V d r).toContinuousLinearEquiv
  letI : NormedAddCommGroup (X→L[ℂ]X):=ContinuousLinearMap.toNormedAddCommGroup
  have ha:Tendsto (fun r=>(A r).toContinuousLinearMap) trail (𝓝 I):=correct F J V lead d
  have hb:=inverted ha
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have uniform:=Frame.compact_event ℝ (isCompact_univ : IsCompact (univ:Set Ratio))
    (fun r t=>dist (exactOp F J V d (r,t)) I<ε) (l:=trail) (fun t _=>by
      let l:=trail ×ˢ 𝓝 t
      have up:l ≤ sweep:=Filter.prod_mono le_rfl le_top
      have hr:Tendsto (fun z:ℝ×Ratio=>z.1) l trail:=tendsto_fst
      have ht:Tendsto (fun z:ℝ×Ratio=>z.2.val) l (𝓝 t.val):=(continuous_subtype_val.tendsto t).comp tendsto_snd
      have hT:Tendsto (exactOp F J V d) l (𝓝 I):=by
        apply Dash.fit_plane (fun z=>(exactOp F J V d z).toLinearMap) I.toLinearMap
        intro v
        have c:=Dash.arcing (ha.comp (bothHomes.mono_left up)) (tendsto_const_nhds (x:=v))
        have o:=Dash.arcing (raw.mono_left up) c
        have g:=engine ht o
        have i:=Dash.arcing (hb.comp hr) g
        have e:=engine (ht.inv₀ (positive t).ne') i
        have got:=e.congr (fun z=>(act F J V z v).symm)
        change Tendsto (fun z=>exactOp F J V d z v) l (𝓝 (I v))
        rw [show Pert.Scale.gear C.labels d t.val⁻¹ ((ContinuousLinearMap.id ℂ X) (Pert.Scale.gear C.labels d t.val ((ContinuousLinearMap.id ℂ X) (I v))))=I v from Pert.Scale.gear_inverse C.labels (positive t).ne' (I v)] at got
        exact got
      exact Metric.tendsto_nhds.mp hT ε hε)
  exact (tendsto_fst.eventually uniform).mono (fun z h=>h z.2 (mem_univ _))

include V in
omit Win in
theorem selected (lead:Leading F J)(d:ℕ):
    ∃v:E d,WilsonPhysicalPositionAdmissible.real C d v=v ∧ ∃a:ℝ,0<a ∧
      ((∀ᶠr in trail,∀t∈Icc (1/2:ℝ) 1,WilsonPhysicalPositionDirectedTest.baseline v-a≤
        WilsonPhysicalPositionDirectedReturn.cross F J v r t)→∀W:RangeSpec,@Raw W G C S J d):=by
  obtain ⟨v,hv,a,ha,branch⟩:=WilsonPhysicalPositionDirectedTest.original F J lead V d
  refine ⟨v,hv,a,ha,?_⟩
  intro paid W
  let X:=E d
  letI : NormedAddCommGroup (X→L[ℂ]X):=ContinuousLinearMap.toNormedAddCommGroup
  unfold Raw
  apply Metric.tendsto_nhds.mpr
  intro ε he
  have done:=branch paid W.left W.positive ε he
  filter_upwards [(tendsto_fst (f:=trail) (g:=(⊤:Filter (@Ratio W)))).eventually done] with z hz
  rw [dist_eq_norm]
  exact hz z.2.val z.2.property (positive z.2)

end YM.Integration.WilsonPositionScaleLawCompactBranch
end
