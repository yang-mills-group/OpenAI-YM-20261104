import YM.Integration.WilsonPositionScaleLawBooked
import YM.Integration.WilsonMeasuredPublicEntranceNativeChange

set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawUniformRepose
open Function Filter Set Spec Table Extraction OPE OPE.Orbits Climb Trace.Pilot PhysMS Maxwell Maxwell.Free
open XSpace XSpace.Normalize
open WilsonPositionScaleLawWindow (RangeSpec Ratio sweep)
open WilsonPositionScaleLawHome (positioned)
open WilsonPositionScaleLawCompactNative
open WilsonPositionScaleLawCompactBranch (Raw)
open WilsonPhysicalPositionUniformBranches (change)
open private expose from YM.Integration.WilsonPhysicalPositionCocycleNative
open private engine from YM.Integration.WilsonPhysicalPositionBornTransition
open scoped Topology Classical
variable [Win:RangeSpec] {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
    (U J:ℝ→tower S)
set_option quotPrecheck false
local notation "E" => (Bel C.book).Field
local notation "move" => WilsonMeasuredPublicEntranceNativeChange.change
open PhysMS.Frame (localCost)

theorem exact {d:ℕ}(z:ℝ×Ratio)(v:E d):
    change J d z.1 z.2.val (positive z.2) v=
      Pert.Scale.gear C.labels d z.2.val⁻¹ (move J U z.1 d (Pert.Scale.gear C.labels d z.2.val
        (change U d z.1 z.2.val (positive z.2) (move U J (z.2.val*z.1) d v)))):=by
  rw [show change J d z.1 z.2.val (positive z.2) v=_ from expose J (positive z.2) v]
  apply congrArg (Pert.Scale.gear C.labels d z.2.val⁻¹)
  change (J z.1 d).symm (J (z.2.val*z.1) d v)=(J z.1 d).symm (U z.1 d
    (Pert.Scale.gear C.labels d z.2.val (Frame.cocycle d U z.1 z.2.val (positive z.2) (move U J (z.2.val*z.1) d v))))
  rw [Frame.cocycle_value d U _ z.2.val z.1 (positive z.2)]
  change (J z.1 d).symm (J (z.2.val*z.1) d v)=(J z.1 d).symm (U (z.2.val*z.1) d ((U (z.2.val*z.1) d).symm (J (z.2.val*z.1) d v)))
  rw [LinearEquiv.apply_symm_apply]

theorem transferred (aligned:localCost trail U J)(d:ℕ)(raw:Raw U d):
    WilsonPhysicalPositionHalfRange.uniform J d Win.left:=by
  let X:=E d
  let I:=ContinuousLinearMap.id ℂ X
  let law(z:ℝ×Ratio):=change J d z.1 z.2.val (positive z.2)
  letI : NormedAddCommGroup (X→L[ℂ]X):=ContinuousLinearMap.toNormedAddCommGroup
  have ha:Tendsto (fun r=>move U J r d) trail (𝓝 I):=(WilsonMeasuredPublicEntranceNativeChange.directions aligned d).1
  have hb:Tendsto (fun r=>move J U r d) trail (𝓝 I):=(WilsonMeasuredPublicEntranceNativeChange.directions aligned d).2
  intro ε hε
  have compact:=Frame.compact_event ℝ (isCompact_univ : IsCompact (univ:Set Ratio))
    (fun r t=>‖law (r,t)-I‖<ε) (l:=trail) (fun t _=>by
      let l:=trail ×ˢ 𝓝 t
      have up:l ≤ sweep:=Filter.prod_mono le_rfl le_top
      have hr:Tendsto (fun z:ℝ×Ratio=>z.1) l trail:=tendsto_fst
      have ht:Tendsto (fun z:ℝ×Ratio=>z.2.val) l (𝓝 t.val):=(continuous_subtype_val.tendsto t).comp tendsto_snd
      have hT:Tendsto law l (𝓝 I):=by
        apply Dash.fit_plane (fun z=>(law z).toLinearMap) I.toLinearMap
        intro v
        have c:=Dash.arcing (ha.comp (bothHomes.mono_left up)) (tendsto_const_nhds (x:=v))
        have o:=Dash.arcing (raw.mono_left up) c
        have g:=engine ht o
        have i:=Dash.arcing (hb.comp hr) g
        have e:=engine (ht.inv₀ (positive t).ne') i
        have got:=e.congr (fun z=>(exact U J z v).symm)
        change Tendsto (fun z=>law z v) l (𝓝 (I v))
        rw [show Pert.Scale.gear C.labels d t.val⁻¹ (I (Pert.Scale.gear C.labels d t.val (I (I v))))=I v
          from Pert.Scale.gear_inverse C.labels (positive t).ne' (I v)] at got
        exact got
      exact (tendsto_iff_norm_sub_tendsto_zero.mp hT).eventually (gt_mem_nhds hε))
  filter_upwards [compact] with r hit t ht pos
  exact hit ⟨t,ht⟩ (mem_univ _)

theorem before (d:ℕ)(h:WilsonPhysicalPositionHalfRange.uniform U d Win.left):Raw U d:=by
  let X:=E d
  letI : NormedAddCommGroup (X→L[ℂ]X):=ContinuousLinearMap.toNormedAddCommGroup
  unfold Raw
  apply Metric.tendsto_nhds.mpr
  intro ε he
  filter_upwards [(tendsto_fst (f:=trail) (g:=(⊤:Filter Ratio))).eventually (h ε he)] with z hz
  rw [dist_eq_norm]
  exact hz z.2.val z.2.property (positive z.2)

omit Win in
theorem original (aligned:localCost trail U J)(held:∀d:ℕ,∀c:ℝ,0<c→WilsonPhysicalPositionHalfRange.uniform U d c):
    ∀d:ℕ,∀c:ℝ,0<c→WilsonPhysicalPositionHalfRange.uniform J d c:=by
  intro d c hc
  letI W:RangeSpec:=⟨c,hc⟩
  have h : WilsonPhysicalPositionHalfRange.uniform U d W.left := held d c hc
  have raw : @Raw W G C S U d := @before W G C S U d h
  exact @transferred W G C S U J aligned d raw
end YM.Integration.WilsonPositionScaleLawUniformRepose
end
