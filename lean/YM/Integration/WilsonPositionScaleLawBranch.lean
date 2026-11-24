import YM.Integration.WilsonPositionScaleLawNative
import YM.Integration.WilsonPhysicalPositionOnePanel

/-! The single reflected margin on the original elected tower selects the
same identity branch after the position normalization at both ends. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawBranch
open Function Filter Set Spec Table Extraction OPE OPE.Orbits Climb Trace.Pilot PhysMS Maxwell Maxwell.Free
open XSpace XSpace.Normalize WilsonPositionScaleLawHome WilsonPositionScaleLawNative
open WilsonPhysicalPositionUniformBranches (change)
open private expose from YM.Integration.WilsonPhysicalPositionCocycleNative
open private engine from YM.Integration.WilsonPhysicalPositionBornTransition
open scoped Topology Classical
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
    (F:Final C f S)(J:ℝ→tower S)(V:Store G)
set_option quotPrecheck false
local notation "E" => (Bel C.book).Field

def Raw (d:ℕ):Prop:=Tendsto (fun z:ℝ×Ratio=>change J d z.1 z.2.val (positive z.2)) sweep
    (𝓝 (ContinuousLinearMap.id ℂ (E d)))

private theorem correct (lead:Leading F J)(d:ℕ):Tendsto
    (fun r=>(WilsonPositionPrescribedFrame.change F J V d r).toContinuousLinearEquiv.toContinuousLinearMap)
    trail (𝓝 (ContinuousLinearMap.id ℂ (E d))):=by
  let X:=E d
  letI : NormedAddCommGroup (X→L[ℂ]X):=ContinuousLinearMap.toNormedAddCommGroup
  exact tendsto_iff_norm_sub_tendsto_zero.mpr (WilsonPositionPrescribedLift.near F J V lead d)

private theorem inverted {X:Type*}[NormedAddCommGroup X][NormedSpace ℂ X][CompleteSpace X]
    {A:ℝ→X≃L[ℂ]X}(h:Tendsto (fun r=>(A r).toContinuousLinearMap) trail (𝓝 (ContinuousLinearMap.id ℂ X))):
    Tendsto (fun r=>(A r).symm.toContinuousLinearMap) trail (𝓝 (ContinuousLinearMap.id ℂ X)):=by
  let I:=ContinuousLinearEquiv.refl ℂ X
  have good:I.toContinuousLinearMap.IsInvertible:=ContinuousLinearMap.isInvertible_equiv
  have inv:=((good.contDiffAt_map_inverse (n:=1)).continuousAt).tendsto.comp h
  have unitInv:I.symm.toContinuousLinearMap=ContinuousLinearMap.id ℂ X:=by ext x;rfl
  simpa only [Function.comp_apply,ContinuousLinearMap.inverse_equiv,unitInv] using
    (show Tendsto (fun r=>(A r).toContinuousLinearMap.inverse) trail (𝓝 I.toContinuousLinearMap.inverse) from inv)

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
theorem selected (lead:Leading F J)(d:ℕ):∃v:E d,WilsonPhysicalPositionAdmissible.real C d v=v ∧
    ∃γ:ℝ,0<γ ∧ ((∀ᶠ r in trail,∀t∈Icc (1/2:ℝ) 1,
      WilsonPhysicalPositionReflectedReturn.reading F J v r t≤γ)→Raw J d):=by
  obtain ⟨v,hv,γ,hγ,h⟩:=WilsonPhysicalPositionOnePanel.original F J lead V d
  refine ⟨v,hv,γ,hγ,?_⟩
  intro vote
  let X:=E d
  letI : NormedAddCommGroup (X→L[ℂ]X):=ContinuousLinearMap.toNormedAddCommGroup
  unfold Raw
  apply Metric.tendsto_nhds.mpr
  intro ε he
  have small:=h (1/2) (by norm_num) vote ε he
  exact (tendsto_fst.eventually small).mono fun z hz=>(dist_eq_norm ..).trans_lt (hz z.2.val z.2.property)

end YM.Integration.WilsonPositionScaleLawBranch
end
