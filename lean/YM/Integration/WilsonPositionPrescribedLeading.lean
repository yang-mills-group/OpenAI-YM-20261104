import YM.Integration.WilsonPositionPrescribedLift
import YM.Integration.WilsonReportPrescribedFrame
import YM.Integration.WilsonPositionThermometerReading

/-! The original physical ribbons can move in their finite-dimensional Maxwell slots. Applying
this to the actual matrices solving the prescribed measuring equations preserves the leading
spatial jets. No rotation rule for the moved frame is required. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionPrescribedLeading
open Function Filter Set MeasureTheory Lattice Wilson RG Source Extraction Table Spec
open PhysicalNext.Repeat.Legato RG17 FullVolume Climb Next.UVStress Trace.Pilot PhysMS
open XSpace XSpace.Normalize XSpace.Rose WilsonPositionThermometerReading
open scoped Topology Classical ContDiff
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book} (F : Final R.family f S)
    (J : ℝ→PhysMS.tower S) (V : Store G) (lead : PhysMS.Leading F J) {Y : (Bel R.family.book).Hierarchy}
    (paid : ∀d : ℕ,∀ᶠ r in Trace.Pilot.trail,PhysMS.Frame.obedient F Y (J r) d)

private theorem fixed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A : ℝ→E →L[ℂ] E) (v : E)
    (h : Tendsto (fun r=>‖A r-ContinuousLinearMap.id ℂ E‖) Trace.Pilot.trail (𝓝 0)) :
    Tendsto (fun r=>A r v) Trace.Pilot.trail (𝓝 v) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  refine squeeze_zero (fun _=>norm_nonneg _) (fun r=>(A r-ContinuousLinearMap.id ℂ E).le_opNorm v) ?_
  simpa only [zero_mul] using h.mul_const ‖v‖

include lead in
theorem applied (d : ℕ) (v : RG17.Free R.family d) :
    Tendsto (fun r=>WilsonPositionPrescribedLift.field F J V d r v) Trace.Pilot.trail (𝓝 v) :=
  fixed (WilsonPositionPrescribedLift.field F J V d) v (WilsonPositionPrescribedLift.near F J V lead d)

include lead paid in
theorem jets {n : ℕ} (d : Caps n) (v : (i : Fin n)→RG17.Free R.family (d i)) (l : ℕ)
    {K : Set (Points n)} (hk : IsCompact K) (hs : K⊆conf n) {ε : ℝ} (he : 0<ε) :
    ∀ᶠ r in Trace.Pilot.trail,∀x∈K,
      ‖iteratedFDeriv ℝ l (fun y=>S.classMoment S d (r • y)
        (fun i=>WilsonPositionPrescribedFrame.positioned F J V r (d i) (v i))) x-
        iteratedFDeriv ℝ l (fun y=>(Bel R.family.book).classMoment (Bel R.family.book) d y v) x‖≤ε :=
  (WilsonReportPrescribedFrame.present F J lead paid).anyJets F J
    (fun r i=>WilsonPositionPrescribedLift.field F J V (d i) r (v i)) v
    (fun i=>applied F J V lead (d i) (v i)) l K hk hs ε he

include lead paid in
theorem roster {n : ℕ} (d : Caps n) (v : (i : Fin n)→RG17.Free R.family (d i))
    {K : Set (Points n)} (hk : IsCompact K) (hs : K⊆conf n) {ε : ℝ} (he : 0<ε) :
    ∀ᶠ r in Trace.Pilot.trail,∀x∈K,
      ‖S.classMoment S d (r • x) (fun i=>WilsonPositionPrescribedFrame.positioned F J V r (d i) (v i))-
        (Bel R.family.book).classMoment (Bel R.family.book) d x v‖≤ε :=
  (WilsonReportPrescribedFrame.present F J lead paid).runs F J
    (fun r i=>WilsonPositionPrescribedLift.field F J V (d i) r (v i)) v
    (fun i=>applied F J V lead (d i) (v i)) K hk hs ε he

include lead paid in
theorem rose (hG : G.Simple) {K : Set (Points 3)} (hk : IsCompact K) (hs : K⊆conf 3) {ε : ℝ} (he : 0<ε) :
    ∀ᶠ r in Trace.Pilot.trail,∀s : Badge,∀x∈K,s.Nonempty →
      ‖sample F (WilsonPositionPrescribedFrame.positioned F J V) r x s‖<ε := by
  apply Filter.eventually_all.mpr
  intro s
  filter_upwards [roster F J V lead paid (fun _ : Fin 3=>6) (leg R.family s) hk hs (half_pos he)] with r bound x hx hne
  have z:=WilsonPositionThermometerReading.free R.family hG (hs hx) s hne
  have b:=bound x hx
  change (Bel R.family.book).classMoment (Bel R.family.book) (fun _ : Fin 3=>6) x (leg R.family s)=0 at z
  rw [z,sub_zero] at b
  exact b.trans_lt (half_lt_self he)

end YM.Integration.WilsonPositionPrescribedLeading
