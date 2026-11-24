import YM.Integration.WilsonOriginalTwoFlatIRPoolRound
import YM.Integration.WilsonOriginalTwoFlatRosePhysical
import YM.Integration.WilsonOriginalTwoFlatIRPoolBook

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatIRPoolLimit
open Function Filter Finset Set Metric MeasureTheory Lattice Wilson RG Source Extraction Table Spec
open Next.UVStress OPE OPE.Orbits Climb Trace Trace.Pilot RG12 RG17 PhysMS PhysicalNext.Repeat.Legato
open XSpace XSpace.Rose Cells Push.GridApprox WilsonPositionThermometerReading
open WilsonThermometerUnitFilingFourSquare
open WilsonOriginalTwoFlatRoseFaceLimits (result names loc)
open WilsonOriginalTwoFlatIRPoolMesh (raw)
open WilsonOriginalTwoFlatIRPoolRound (rounded)
open WilsonReceivedChronologicalFixedRoseVariation (signed)
open WilsonOriginalTwoFlatIRSocketHeardCell (incumbent)
open WilsonOriginalTwoFlatIRPoolBook (direct)
open WilsonOriginalTwoFlatRosePhysical (continuum)
open WilsonNeutralOffsetCutoff (named)
open WilsonPositionThermometerGradedSource (grade)
open WilsonPositionThermometerConnected (value)
open scoped Topology Classical BigOperators

variable {G:Gauge}(R:Run G){order:Extraction.Order}{S:Table R.family.book}
    (F:Final R.family order S){Y:Ultrafilter (ℕ×ℕ)}
local notation "d" => fun i:Fin 3=>(grade i).val
local notation "E" => Finset (Fin 3)
variable (v:(i:Fin 3)→S.Field (d i))(arms:(i:Fin 3)→Arm R.family S (Y:Filter _) (d i) (v i))
include F in
theorem physical (hG:G.Simple)(hl:(Y:Filter _)≤order.fuse)(r:ℝ)(rp:0<r)
    {K:Set (Points 3)}(compact:IsCompact K)(sep:K⊆conf 3){ε:ℝ}(ep:0<ε):
    ∀ᶠ z:UVIndex in (Y:Filter _),∀x∈K,dist (value (raw R r z (fun i=>(arms i).source z) x)) (value (result R r v x))<ε:=by
  let V:=result R r v '' K
  have cv:IsCompact V:=compact.image_of_continuousOn ((continuum R F v rp).mono sep)
  let W:=cthickening (1:ℝ) V
  have cw:IsCompact W:=cv.cthickening
  obtain ⟨δ,dp,move⟩:=Metric.uniformContinuousOn_iff.mp
    (cw.uniformContinuousOn_of_continuous WilsonPositionThermometerConnected.continuous_value.continuousOn) ε ep
  have pos:0 < min 1 δ:=lt_min one_pos dp
  filter_upwards [WilsonOriginalTwoFlatIRPoolMesh.limit R F hG hl r rp v arms compact sep pos]
    with z seen x hx
  have near:dist (raw R r z (fun i=>(arms i).source z) x) (result R r v x) < min 1 δ:=(dist_pi_lt_iff pos).mpr (fun s=>seen s x hx)
  have av:result R r v x∈V:=⟨x,hx,rfl⟩
  have aw:raw R r z (fun i=>(arms i).source z) x∈W:=mem_cthickening_of_dist_le _ _ 1 V av (near.le.trans (min_le_left _ _))
  exact move _ aw _ (self_subset_cthickening V av) (near.trans_le (min_le_right _ _))


/-- Every one of the seven finite Wilson numerators uses the original N-site
above the same physical f cell. -/
theorem at_cut (r:ℝ)(rp:0<r)(φ:Test 3){f:ℕ}(z:UVIndex)(live:f≤z.1)
    (heads:(i:Fin 3)→R.family.label (d i)):
    signed R φ r (f,z.2) (fun o=>value (incumbent R (N:=z.1) heads (fun _=>direct) o.val))=
    ∫x,φ x*value (raw R r z heads (rounded R r f x)):=by
  rw [WilsonOriginalTwoFlatIRPoolRound.weighted R φ r (f,z.2) (fun o=>value (incumbent R (N:=z.1) heads (fun _=>direct) o))]
  apply integral_congr_ae
  filter_upwards with x
  congr 1
  apply congrArg WilsonPositionThermometerConnected.value
  funext s
  unfold WilsonOriginalTwoFlatIRSocketHeardCell.incumbent WilsonOriginalTwoFlatIRPoolMesh.raw
  rw [WilsonOriginalTwoFlatIRPoolChamber.labelled live heads (fun _=>direct) _ s heads
    (fun i=>WilsonOriginalTwoFlatIRPoolBook.target (R:=R) _ _)]
  congr 1;congr 1;funext i
  exact (WilsonOriginalTwoFlatIRPoolRound.placement R r rp live z.2 x i).symm

include F in
/-- At fixed physical r the nonlinear, signed finite compact Wilson experiment
converges to the public continuum quadrature with those same embedded cells. -/
theorem original (hG:G.Simple)(hl:(Y:Filter _)≤order.fuse)(r:ℝ)(rp:0<r)(φ:Test 3){τ:ℝ}
    (confined:cthickening τ (tsupport (φ:Points 3→ℂ))⊆conf 3)(f:ℕ)
    (small:4*(3:ℝ)*R.family.S.a f≤τ*r):
    Tendsto (fun z:UVIndex=>signed R φ r (f,z.2) (fun o=>value (incumbent R (N:=z.1)
      (fun i=>(arms i).source z) (fun _=>direct) o.val))) (Y:Filter _)
      (𝓝 (∫x,φ x*value (result R r v (rounded R r f x)))):=by
  let K:=cthickening τ (tsupport (φ:Points 3→ℂ))
  have kc:IsCompact K:=φ.hasCompactSupport.cthickening
  let read(x:Points 3):=value (result R r v x)
  have smooth:ContinuousOn read K:=WilsonPositionThermometerConnected.continuous_value.comp_continuousOn
    ((continuum R F v rp).mono confined)
  obtain ⟨C,cap⟩:=(kc.image_of_continuousOn smooth).isBounded.exists_norm_le
  let u(x:Points 3):=read (rounded R r f x)
  have um:Measurable u:=WilsonOriginalTwoFlatIRPoolRound.field R r f read
  have gi:Integrable (fun x:Points 3=>φ x) volume:=φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  have oi:Integrable (fun x:Points 3=>φ x*u x):=(gi.norm.mul_const C).mono' (φ.continuous.measurable.mul um).aestronglyMeasurable
    (Eventually.of_forall fun x=>by
      by_cases hit:φ x=0
      · simp [hit]
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (cap _ ⟨_,WilsonOriginalTwoFlatIRPoolRound.near R φ rp small hit,rfl⟩) (norm_nonneg _))
  apply Metric.tendsto_nhds.mpr
  intro ε ep
  let wt:=∫x:Points 3,‖φ x‖
  have wp:0≤wt:=integral_nonneg (fun x=>norm_nonneg _)
  let t:=ε/(2*(1+wt))
  have tp:0<t:=by dsimp [t];positivity
  have price:wt*t<ε:=by dsimp [t];rw [mul_div_assoc',div_lt_iff₀ (by positivity)];nlinarith [mul_nonneg wp ep.le]
  filter_upwards [physical R F v arms hG hl r rp kc confined tp,(large_mesh order f).filter_mono hl] with z close live
  let y(x:Points 3):=value (raw R r z (fun i=>(arms i).source z) (rounded R r f x))
  have meas:Measurable y:=WilsonOriginalTwoFlatIRPoolRound.field R r f (fun b=>value (raw R r z (fun i=>(arms i).source z) b))
  have point(x:Points 3):‖φ x*y x-φ x*u x‖≤‖φ x‖*t:=by
    by_cases hit:φ x=0
    · simp [hit]
    · rw [←mul_sub,norm_mul]
      exact mul_le_mul_of_nonneg_left (by simpa [dist_eq_norm] using (close _ (WilsonOriginalTwoFlatIRPoolRound.near R φ rp small hit)).le) (norm_nonneg _)
  have di:Integrable (fun x:Points 3=>φ x*y x-φ x*u x):=(gi.norm.mul_const t).mono'
    ((φ.continuous.measurable.mul meas).sub (φ.continuous.measurable.mul um)).aestronglyMeasurable (Eventually.of_forall point)
  have yi:Integrable (fun x:Points 3=>φ x*y x):=(di.add oi).congr (Eventually.of_forall fun _=>sub_add_cancel _ _)
  rw [at_cut R r rp φ z live,dist_eq_norm]
  change ‖(∫x,φ x*y x)-(∫x,φ x*u x)‖<ε
  rw [←integral_sub yi oi]
  refine (norm_integral_le_of_norm_le (gi.norm.mul_const t) (Eventually.of_forall point)).trans_lt ?_
  rw [integral_mul_const]
  exact price

end YM.Integration.WilsonOriginalTwoFlatIRPoolLimit
end
