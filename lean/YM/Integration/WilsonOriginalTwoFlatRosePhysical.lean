import YM.Integration.WilsonOriginalTwoFlatRoseFaceLimits

/-! The original microscopic signed Rose on one physical extraction. All proper moments
are measured at the same rounded positions before the connected polynomial and smearing. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatRosePhysical
open Function Filter Finset Set Metric MeasureTheory Lattice Wilson RG Source Extraction Table Spec
open OPE OPE.Orbits Climb Trace Trace.Pilot RG12 RG17 PhysMS PhysicalNext.Repeat.Legato
open XSpace XSpace.Rose Cells Push.GridApprox WilsonPositionThermometerReading
open WilsonThermometerUnitFilingFourSquare
open WilsonOriginalTwoFlatRoseFaceLimits (raw result names loc)
open WilsonNeutralOffsetCutoff (named)
open WilsonPositionThermometerGradedSource (grade)
open WilsonPositionThermometerConnected (value)
open scoped Topology Classical BigOperators
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}
    (F:Final R.family f S)(A:WilsonPositionThermometerCapStation.Group R.family 6)
    {Y:Ultrafilter (ℕ×ℕ)}
local notation "d" => fun i:Fin 3=>(grade i).val
local notation "E" => Finset (Fin 3)
variable (v:(i:Fin 3)→S.Field (d i))
    (arms:(i:Fin 3)→Arm R.family S (Y:Filter _) (d i) (v i))
    (same:∀z i,(arms i).source z=named R A z.1 z.2 i)

include F in
theorem continuum {r:ℝ}(hr:0<r):ContinuousOn (result R r v) (conf 3):=by
  apply continuousOn_pi.mpr
  intro s
  let τ (j):S.Tag:=⟨d (names s j).val,v (names s j).val⟩
  apply (S.class_smooth S F.room.kernel.smooth τ).continuousOn.comp
  · exact ((continuous_const_smul r).comp (WilsonOriginalTwoFlatRoseFaceLimits.continuous_loc s)).continuousOn
  · exact fun x hx=>Work.A05.smul_conf hr (WilsonOriginalTwoFlatRoseFaceLimits.separate s hx)

include F A arms same in
theorem physical (hG:G.Simple)(hl:(Y:Filter _)≤f.fuse)(r:ℝ)(rp:0<r)
    {K:Set (Points 3)}(compact:IsCompact K)(sep:K⊆conf 3){ε:ℝ}(ep:0<ε):
    ∀ᶠ z:UVIndex in (Y:Filter _),∀x∈K,dist (value (raw R A r z x)) (value (result R r v x))<ε:=by
  let V:=result R r v '' K
  have cv:IsCompact V:=compact.image_of_continuousOn ((continuum R F v rp).mono sep)
  let W:=cthickening (1:ℝ) V
  have cw:IsCompact W:=cv.cthickening
  obtain ⟨δ,dp,move⟩:=Metric.uniformContinuousOn_iff.mp
    (cw.uniformContinuousOn_of_continuous WilsonPositionThermometerConnected.continuous_value.continuousOn) ε ep
  have pos:0 < min 1 δ:=lt_min one_pos dp
  filter_upwards [WilsonOriginalTwoFlatRoseFaceLimits.original R F A hG hl r rp v arms same compact sep pos]
    with z seen x hx
  have near:dist (raw R A r z x) (result R r v x) < min 1 δ:=(dist_pi_lt_iff pos).mpr (fun s=>seen s x hx)
  have av:result R r v x∈V:=⟨x,hx,rfl⟩
  have aw:raw R A r z x∈W:=mem_cthickening_of_dist_le _ _ 1 V av (near.le.trans (min_le_left _ _))
  exact move _ aw _ (self_subset_cthickening V av) (near.trans_le (min_le_right _ _))

include F A arms same in
theorem original (hG:G.Simple)(hl:(Y:Filter _)≤f.fuse)(r:ℝ)(rp:0<r)(φ:Test 3):
    Tendsto (fun z=>φ.applyTo (fun x=>value (raw R A r z x))) (Y:Filter _)
      (𝓝 (φ.applyTo (fun x=>value (result R r v x)))):=by
  apply Metric.tendsto_nhds.mpr
  intro ε ep
  let wt:=∫x:Points 3,‖φ x‖
  have wp:0≤wt:=integral_nonneg (fun x=>norm_nonneg _)
  let t:=ε/(2*(1+wt))
  have tp:0<t:=by dsimp [t];positivity
  have price:wt*t<ε:=by dsimp [t];rw [mul_div_assoc',div_lt_iff₀ (by positivity)];nlinarith [mul_nonneg wp ep.le]
  let u(x:Points 3):=value (result R r v x)
  have oi:Integrable (fun x:Points 3=>φ x*u x):=φ.smearing
    (WilsonPositionThermometerConnected.continuous_value.comp_continuousOn (continuum R F v rp))
  have gi:Integrable (fun x:Points 3=>φ x) volume:=φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  filter_upwards [physical R F A v arms same hG hl r rp φ.hasCompactSupport φ.tsupport_subset tp] with z close
  let y(x:Points 3):=value (raw R A r z x)
  have meas:Measurable y:=
    (measurable_of_finite (fun o:Fin 3→Site (R.family.side z.1 z.2)=>value (fun s:E=>
      R.family.omega z.1 z.2 fun U=>∏i∈s,R.family.O z.1 z.2 (named R A z.1 z.2 i) (o i) U))).comp
      (WilsonSeparatedOriginalThermometerCells.placed (R:=R) r z)
  have point(x:Points 3):‖φ x*y x-φ x*u x‖≤‖φ x‖*t:=by
    by_cases hz:φ x=0
    · simp [hz]
    rw [←mul_sub,norm_mul]
    exact mul_le_mul_of_nonneg_left (le_of_lt (by simpa only [dist_eq_norm] using close x (subset_closure hz))) (norm_nonneg _)
  have di:Integrable (fun x:Points 3=>φ x*y x-φ x*u x):=(gi.norm.mul_const t).mono'
    ((φ.continuous.measurable.mul meas).aestronglyMeasurable.sub oi.aestronglyMeasurable) (Eventually.of_forall point)
  have yi:Integrable (fun x:Points 3=>φ x*y x):=(di.add oi).congr (Eventually.of_forall fun _=>sub_add_cancel _ _)
  rw [dist_eq_norm]
  change ‖(∫x,φ x*y x)-(∫x,φ x*u x)‖<ε
  rw [←integral_sub yi oi]
  refine (norm_integral_le_of_norm_le (gi.norm.mul_const t) (Eventually.of_forall point)).trans_lt ?_
  rw [integral_mul_const]
  exact price

end YM.Integration.WilsonOriginalTwoFlatRosePhysical
end
