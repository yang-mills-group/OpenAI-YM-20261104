import YM.Integration.WilsonPositionHomogeneousFrame
import YM.Integration.WilsonReportingMeasuredAdmission

/-! Zeroth order of the manuscript's homogeneous-frame comparison, for actual
joint physical fields of arbitrary arity, and all fixed spatial derivatives
uniformly on every compact subset of the separated configurations. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionHomogeneousLeading
open Function Filter Set MeasureTheory Lattice Wilson RG Source Extraction Table Spec
open PhysicalNext.Repeat.Legato RG17 FullVolume Climb Next.UVStress Trace.Pilot PhysMS
open Maxwell XSpace XSpace.Normalize FVA2 FVA2.Register
open WilsonPositionHomogeneousFrame
open private leg from YM.Integration.WilsonPositionHomogeneousFrame
open scoped Topology ContDiff Classical
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    (F : Final R.family f S) (J : ℝ→PhysMS.tower S) (Z : WilsonPrescription G)
    (lead : PhysMS.Leading F J) {Y : (Bel R.family.book).Hierarchy}
    (paid : ∀d : ℕ,∀ᶠ r in Trace.Pilot.trail,PhysMS.Frame.obedient F Y (J r) d)

private def value {d : ℕ} (v : Sec G d) : Change G d→ₗ[ℝ] Sec G d where
  toFun u:=u.val v
  map_add' _ _:=rfl
  map_smul' _ _:=rfl

private def column (d : ℕ) (v : RG17.Free R.family d) : MoveSpace G d→ₗ[ℝ] RG17.Free R.family d :=
  ((Maxwell.Free.fields R.family.labels d).symm.toLinearMap.restrictScalars ℝ).comp
    ((value ((Maxwell.Free.fields R.family.labels d) v)).comp (guide G d).symm.toLinearMap)

private theorem column_apply {d : ℕ} (v : RG17.Free R.family d) (u : Change G d) :
    column d v (guide G d u) = (Maxwell.Free.fields R.family.labels d).symm (u.val ((Maxwell.Free.fields R.family.labels d) v)) := by
  change (Maxwell.Free.fields R.family.labels d).symm (((guide G d).symm (guide G d u)).val _)=_
  rw [LinearEquiv.symm_apply_apply]

private theorem projected {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (L : E→ₗ[ℝ]V) {a : ℝ→E} (hx:Tendsto a Trace.Pilot.trail (𝓝 0)) :
    Tendsto (fun r=>L (a r)) Trace.Pilot.trail (𝓝 0) := by
  have ht:Tendsto (fun r=>L (a r)) Trace.Pilot.trail (𝓝 (L 0)) := (L.continuous_of_finiteDimensional.tendsto 0).comp hx
  simpa only [map_zero] using ht

private theorem shifted {E : Type*} [NormedAddCommGroup E] {a : ℝ→E} (v:E) (hx:Tendsto a Trace.Pilot.trail (𝓝 0)) :
    Tendsto (fun r=>v+a r) Trace.Pilot.trail (𝓝 v) := by
  simpa only [add_zero] using (tendsto_const_nhds (x:=v)).add hx

private theorem operate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A:ℝ→E→L[ℂ]E) (x:ℝ→E) (v:E)
    (hm:Tendsto (fun r=>‖A r-ContinuousLinearMap.id ℂ E‖) Trace.Pilot.trail (𝓝 0))
    (hx:Tendsto x Trace.Pilot.trail (𝓝 v)) :
    Tendsto (fun r=>A r (x r)) Trace.Pilot.trail (𝓝 v) := by
  have h:Tendsto A Trace.Pilot.trail (𝓝 (ContinuousLinearMap.id ℂ E)) := tendsto_iff_norm_sub_tendsto_zero.mpr hm
  have ev : Continuous (fun z : (E→L[ℂ]E)×E=>z.1 z.2) := by fun_prop
  exact (ev.tendsto (ContinuousLinearMap.id ℂ E,v)).comp (h.prodMk_nhds hx)

include lead paid in
theorem moved (hG:G.Simple) (d : ℕ) (v : RG17.Free R.family d) :
    Tendsto (fun r=>change F J Z d r v) Trace.Pilot.trail (𝓝 v) := by
  have hw : Tendsto (reading F J Z) Trace.Pilot.trail (𝓝 0) :=
    WilsonPositionPrescribedZero.measured F J Z.store lead paid hG Z.criterion
  have hn : Tendsto (fun r=>guide G d (turn F J Z d r)) Trace.Pilot.trail (𝓝 0) := (WilsonPositionHomogeneousNear.near Z d).comp hw
  apply (shifted v (projected (column d v) hn)).congr'
  filter_upwards [fitted F J Z lead paid hG d] with r fit
  rw [column_apply]
  have h:=leg F J Z fit ((Maxwell.Free.fields R.family.labels d) v)
  simpa only [stood,map_add,LinearEquiv.symm_apply_apply] using h.symm

include lead paid in
theorem field (hG:G.Simple) (d : ℕ) (v : RG17.Free R.family d) :
    Tendsto (fun r=>WilsonPositionPrescribedLift.field F J Z.store d r (change F J Z d r v)) Trace.Pilot.trail (𝓝 v) :=
  operate (WilsonPositionPrescribedLift.field F J Z.store d) (fun r=>change F J Z d r v) v
      (WilsonPositionPrescribedLift.near F J Z.store lead d) (moved F J Z lead paid hG d v)

include lead paid in
theorem jets (hG:G.Simple) {n : ℕ} (d : Caps n) (v : (i : Fin n)→RG17.Free R.family (d i)) (l : ℕ)
    {K : Set (Points n)} (hk : IsCompact K) (hs : K⊆conf n) {ε : ℝ} (he : 0<ε) :
    ∀ᶠ r in Trace.Pilot.trail,∀x∈K,
      ‖iteratedFDeriv ℝ l (fun y=>S.classMoment S d (r • y)
        (fun i=>homogeneous F J Z r (d i) (v i))) x-
        iteratedFDeriv ℝ l (fun y=>(Bel R.family.book).classMoment (Bel R.family.book) d y v) x‖≤ε :=
  (WilsonReportingMeasuredAdmission.present F J lead paid).anyJets F J
    (fun r i=>WilsonPositionPrescribedLift.field F J Z.store (d i) r (change F J Z (d i) r (v i))) v
    (fun i=>field F J Z lead paid hG (d i) (v i)) l K hk hs ε he

end YM.Integration.WilsonPositionHomogeneousLeading

