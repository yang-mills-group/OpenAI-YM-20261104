import YM.Integration.WilsonPositionReflectedTubeInputs
import YM.Integration.WilsonFiniteReflectedMatrix
import YM.GapsContact.Slab.VacGram

/-! Operator control of the actual reflected physical Gram on every bounded ball of independent
fixed-degree sources. Scales may select the fields and their prescribed frames independently. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonNormalizedReflectedForm
open Function Filter Set Metric Extraction Table Spec Climb PhysMS Maxwell OPE OPE.Levy Trace.Pilot
open YM.Push.FiniteDetection.Free XSpace XSpace.Normalize GapsContact
open WilsonPositionReflectedTubeInputs
open scoped Topology Classical
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (J : ℝ → PhysMS.tower S) (V : Store G)

def fitted (d : ℕ) (r : ℝ) : RG17.Free C d →ₗ[ℂ] RG17.Free C d →ₗ[ℂ] ℂ :=
  linear₂ ((S.classMoment S (fun _ : Fin 2=>d) (r • detectors)).compLinearMap (fun _=>(J r d).toLinearMap))

private def toOp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (b : E →ₗ[ℂ] E →ₗ[ℂ] ℂ) : E →ₗ[ℂ] E →L[ℂ] ℂ where
  toFun v := (b v).toContinuousLinearMap
  map_add' v w := by ext z; change b (v+w) z=b v z+b w z; rw [map_add]; rfl
  map_smul' c v := by ext z; change b (c • v) z=c • b v z; rw [map_smul]; rfl

theorem operator (lead : PhysMS.Leading F J) (d : ℕ) : Tendsto
    (fun r=>(toOp (fitted J d r)).toContinuousLinearMap) trail
    (𝓝 (toOp (initial C d)).toContinuousLinearMap) := by
  apply Dash.fit_plane
  intro u
  apply Dash.fit_plane
  intro w
  exact PhysMS.leading_at F lead (d:=fun _ : Fin 2=>d) ![u,w] tendsto_id tendsto_const_nhds detectors_in

private theorem actual (d : ℕ) (r : ℝ) (hr : Spin.realH F.room.kernel.spin (Maxwell.Free.spin_free C.labels) (J r d))
    (v : RG17.Free C d) : fitted J d r v (reflect d v) = reflected F d r (J r d v) := by
  unfold fitted reflected
  change S.classMoment S _ (r • detectors) (fun i : Fin 2=> J r d (![v,reflect d v] i)) = _
  apply DFunLike.congr_arg
  funext i
  fin_cases i
  · rfl
  · exact PhysMS.Frame.flip_coupled F d J r hr v

def field (frame : Bool) (d : ℕ) (r : ℝ) (v : RG17.Free C d) : S.Field d :=
  if frame then WilsonPositionPrescribedFrame.positioned F J V r d v else J r d v

theorem uniform (lead : PhysMS.Leading F J) (d : ℕ) {T : ℝ} (hT : 0≤T) :
    ∃ B : ℝ, 0≤B ∧ ∀ᶠ r in trail, ∀ (frame : Bool) (v : RG17.Free C d), ‖v‖≤T →
    Ascent.cost F d r (field F J V frame d r v)≤B := by
  let E := RG17.Free C d
  let L := ‖ContinuousLinearMap.id ℂ E‖+1
  let U := L*T
  have hL : 1≤L := by dsimp [L]; linarith [norm_nonneg (ContinuousLinearMap.id ℂ E)]
  have hU : 0≤U := mul_nonneg (zero_le_one.trans hL) hT
  have hrfl : Continuous (reflect (C:=C) d) := continuous_iff_continuousAt.mpr
    (fun v=>reflect_limit d (tendsto_id : Tendsto id (𝓝 v) (𝓝 v)))
  obtain ⟨b,hb⟩ := ((isCompact_closedBall (0:E) U).image hrfl.norm).bddAbove
  have entry (x y : E) : Tendsto (fun r=>fitted J d r x y) trail (𝓝 (initial C d x y)) :=
    PhysMS.leading_at F lead (d:=fun _ : Fin 2=>d) ![x,y] tendsto_id tendsto_const_nhds detectors_in
  obtain ⟨Q,-,bounded⟩ := WilsonFiniteReflectedMatrix.bounded trail (initial C d) (fitted J d) entry hU (le_max_left 0 b)
  refine ⟨Real.sqrt Q,Real.sqrt_nonneg _,?_⟩
  filter_upwards [bounded,lead.equivariant d,
    WilsonPositionPrescribedLift.fee F J V lead d] with r bill coherent changeCost
  have bound (w : E) (hw : ‖w‖≤U) : Ascent.cost F d r (J r d w)≤Real.sqrt Q := by
    change Real.sqrt ‖reflected F d r (J r d w)‖ ≤ _
    rw [←actual F J d r coherent w]
    apply Real.sqrt_le_sqrt
    have hrw : ‖reflect d w‖≤ max 0 b := (hb (mem_image_of_mem _ (show w∈closedBall 0 U by simpa using hw))).trans (le_max_right _ _)
    exact bill w (reflect d w) hw hrw
  intro frame v hv
  cases frame
  · exact bound v (hv.trans (le_mul_of_one_le_left hT hL))
  · exact bound (WilsonPositionPrescribedLift.field F J V d r v) (((WilsonPositionPrescribedLift.field F J V d r).le_opNorm v).trans
      (mul_le_mul changeCost hv (norm_nonneg _) (zero_le_one.trans hL)))

end YM.Integration.WilsonNormalizedReflectedForm
