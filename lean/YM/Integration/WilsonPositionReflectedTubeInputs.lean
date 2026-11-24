import YM.Integration.WilsonPositionPrescribedLift
import YM.PhysMS.Frame.Step

/-! Reflected antipodal measurements of the actual position-scheme fields. The
independent fixed field on the right is the one in the original free table. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionReflectedTubeInputs
open Function Filter Set Extraction Table Spec Climb PhysMS Maxwell OPE OPE.Levy Trace.Pilot
open YM.Push.FiniteDetection.Free
open XSpace XSpace.Normalize
open scoped Topology Classical
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (J : ℝ → PhysMS.tower S) (V : Store G)

/-- The second field is the time-reflected complex conjugate in this same physical table. -/
def reflected (d : ℕ) (r : ℝ) (y : S.Field d) : ℂ :=
  S.classMoment S (fun _ : Fin 2 => d) (r • detectors)
    ![y,S.mirror F.room.kernel.spin d (Signed.mirror timeAxis) (S.conj F.room.kernel.spin d y)]

private def gram (d : ℕ) (r : ℝ) : RG17.Free C d →ₗ[ℂ] RG17.Free C d →ₗ[ℂ] ℂ :=
  linear₂ ((S.classMoment S (fun _ : Fin 2 => d) (r • detectors)).compLinearMap
    (fun _ => (J r d).toLinearMap))

def initial (C : Family G) (d : ℕ) : RG17.Free C d →ₗ[ℂ] RG17.Free C d →ₗ[ℂ] ℂ :=
  linear₂ ((Bel C.book).classMoment (Bel C.book) (fun _ : Fin 2 => d) detectors)

private theorem entry (lead : PhysMS.Leading F J) (d : ℕ) (p q : RG17.Free C d) :
    Tendsto (fun r => gram J d r p q) trail (𝓝 (initial C d p q)) :=
  PhysMS.leading_at F lead (d:=fun _ : Fin 2 => d) ![p,q] tendsto_id tendsto_const_nhds detectors_in

private theorem varies {D : Type*} [NormedAddCommGroup D] [NormedSpace ℂ D]
    [FiniteDimensional ℂ D] {a : ℝ → D →ₗ[ℂ] D →ₗ[ℂ] ℂ} {b : D →ₗ[ℂ] D →ₗ[ℂ] ℂ}
    (pin : ∀ x y, Tendsto (fun r => a r x y) trail (𝓝 (b x y))) {p q : ℝ → D}
    {u v : D} (hp : Tendsto p trail (𝓝 u)) (hq : Tendsto q trail (𝓝 v)) :
    Tendsto (fun r => a r (p r) (q r)) trail (𝓝 (b u v)) := by
  let B (r : ℝ) := a r (p r)
  apply Dash.arcing (W:=fun r => (B r).toContinuousLinearMap)
    (X:=(b u).toContinuousLinearMap) ?_ hq
  apply Dash.fit_plane B (b u)
  intro w
  exact Dash.arcing (Dash.fit_plane (fun r => LinearMap.comp (LinearMap.applyₗ (R:=ℂ) w) (a r))
    (LinearMap.comp (LinearMap.applyₗ (R:=ℂ) w) b) (fun x => pin x w)) hp

/-- Limit of the full complex reflected Gram; both arguments may move in the true finite source space. -/
theorem measured (lead : PhysMS.Leading F J) (d : ℕ) {w : ℝ → RG17.Free C d}
    {v : RG17.Free C d} (hw : Tendsto w trail (𝓝 v)) :
    Tendsto (fun r => reflected F d r (J r d (w r))) trail
      (𝓝 (initial C d v (reflect d v))) := by
  apply (varies (a:=gram J d) (b:=initial C d) (entry F J lead d) hw (reflect_limit d hw)).congr'
  filter_upwards [lead.equivariant d] with r hr
  unfold gram reflected
  change S.classMoment S _ (r • detectors) (fun i : Fin 2 => J r d (![w r,reflect d (w r)] i)) = _
  apply DFunLike.congr_arg
  funext i
  fin_cases i
  · rfl
  · exact PhysMS.Frame.flip_coupled F d J r hr (w r)

/-- The admitted position-scheme change acts on these original source coordinates before the physical map. -/
theorem changed (lead : PhysMS.Leading F J) (d : ℕ) (v : RG17.Free C d) :
    Tendsto (fun r => reflected F d r (WilsonPositionPrescribedFrame.positioned F J V r d v)) trail
      (𝓝 (initial C d v (reflect d v))) := by
  apply measured F J lead d (w:=fun r => WilsonPositionPrescribedLift.field F J V d r v)
  have h := WilsonPositionPrescribedLift.near F J V lead d
  rw [Metric.tendsto_nhds] at h ⊢
  intro ε he
  have hp : 0 < ε / (‖v‖+1) := div_pos he (by positivity)
  filter_upwards [h _ hp] with r hr
  let A := WilsonPositionPrescribedLift.field F J V d r - ContinuousLinearMap.id ℂ (RG17.Free C d)
  have hA : ‖A‖ < ε/(‖v‖+1) :=
    (le_abs_self ‖A‖).trans_lt (by simpa only [A,Real.dist_eq,sub_zero] using hr)
  rw [dist_eq_norm]
  change ‖A v‖ < ε
  calc ‖A v‖ ≤ ‖A‖*‖v‖ := A.le_opNorm v
       _ ≤ ‖A‖*(‖v‖+1) := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) (norm_nonneg A)
       _ < ε := (lt_div_iff₀ (by positivity : 0<‖v‖+1)).mp hA

end YM.Integration.WilsonPositionReflectedTubeInputs
