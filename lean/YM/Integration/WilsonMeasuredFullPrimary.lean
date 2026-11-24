import YM.Integration.WilsonMeasuredMarkedPrimary
import YM.Integration.WilsonMeasuredCourseSourceGerm
import YM.Integration.ActualWilsonPrimaryPreparation
import YM.Trace.Physicalv2.GermSplit

/-! Evaluate the singleton of the complete marked density on the same measured vacuum,
and hear its signed projection on the original Wilson history. The paid regular
term controls the primary, including its scalar coordinate. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredFullPrimary
open Function Set Finset Filter Lattice Wilson RG Marker Overlay Source Labels RG.Shoot
open Push.Local RG3.Primary QuadraticLocal Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open Extra.Histories RG16.Guarding Relay PhysicalNext Repeat Legato Graces Roost
open Pressure Testing Input Precision Org Supply Push SectorMeasure PriceCompiler
open ConnectedActivityE6 Progress.DirectedRecipe AllOrder AllOrder.Transit WheelP AllOrder.Floe QuadraticLocal.Advent
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge} {V T ι:Type} [Fintype V] [DecidableEq V] {B:Census V}

theorem healthy {n:Side} {o:V→Site n} {W:Rep G n} (L:Gallery T ι o W B)
    {θ:V→ℝ} (hw:∀ v,0<θ v) {reg:ℝ} (regular:L.E.Paid θ W.p.B (W.p.supportExponent+2) reg)
    (t:T) (v:V) (U:Config G n) (clear:flags W.p.threshold U=∅) :
    (L.density t U).part (B.fire v)=(W.eval U:ℂ)*(L.E.log t U).part (B.fire v) := by
  have gas : L.gas t U=1 := by
    unfold Gallery.gas
    rw [tsum_eq_single ∅]
    · have h : W.activities.admissible W.p U ∅ := by simp [Activities.admissible,clear]
      simp [Fusion.Attached.packet,h]
    intro S hS
    have bad:¬W.activities.admissible W.p U S := by
      intro ha
      obtain ⟨j,hj⟩:=Finset.nonempty_iff_ne_empty.mpr hS
      obtain ⟨y,hy⟩:=(W.activities.forced j).inventory_ne
      have mem:y∈flags W.p.threshold U := by
        rw [←ha.2]
        exact Finset.mem_biUnion.mpr ⟨j,hj,hy⟩
      simp [clear] at mem
    simp [Fusion.Attached.packet,bad]
  have quiet := L.E.quiet_of_hasSum t U (regular.sums (by linarith [W.p.exponent_pos]) hw t U)
  rw [Gallery.density,gas,mul_one,Poly.part_smul,MergeProof.Accent.whisper B _ quiet v,
    Rep.eval,W.activities.gas_one (p:=W.p) clear,mul_one]

variable [Nonempty V] [Nonempty T] [Countable ι]

theorem original (R:Run G) {i m N per k d:ℕ} (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin)
    (Ψ:∀ j,Rep G (R.family.side j per)) (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (started:m ≤ i) (live:i ≤ N) (opened:Opened R.family d i per)
    {o:V→Site (R.family.side i per)} (L:Gallery T ι o (Ψ i) B) {θ:V→ℝ} {reg hard:ℝ}
    (hw:∀v,0<θ v) (valid:(Ψ i).activities.ForcedFamily (Ψ i).p)
    (regular:L.E.Paid θ (Ψ i).p.B ((Ψ i).p.supportExponent+2) reg)
    (forced:L.K.Paid θ (Ψ i).p.B (Ψ i).p.supportExponent hard) (x:T) (v:V) (root:o v=0) :
    let C:=R.family
    let W:=Ψ i
    let sec:=C.localSection d
    let w:=Next.Foundations.price G (max W.p.order W.p.power)
    let r:=4*reg
    let s:=(factor C.params sec W.p.supportExponent w * (W.p.order.factorial:ℝ))*r
    let c:=(W.p.order.factorial:ℝ)*r+s+θ v*W.p.mass (sec.footprint (0 : Site (C.side i per))) (w*(s/θ v))
    let h:=max (c/θ v) (2*(r+s)/θ v)
    ∃ q:store C d per i, reads (C:=C) d N per i q (c/θ v) ∧ q.forced=0 ∧
      (fun U=>(L.density x U).part (B.fire v)) =ᶠ[𝓝 1] value (C:=C) d N per i q ∧
      (C.labels.level d).coeffSize (page (C:=C) d per i q) ≤ 2*h ∧
      ∀ f u a, Ink C N per d i f u a →
        f =ᶠ[𝓝 1] (fun U=>(L.density x U).part (B.fire v)) → u=page (C:=C) d per i q := by
  intro C W sec w r s c h
  obtain ⟨point,-,-⟩:= WilsonMeasuredCourseQuietSlots.selected R π Γ Ψ course started live
  change (C.path.rep N per i).p=W.p at point
  have he : Readable C.params sec W.p (C.side i per) w := by
    dsimp only [w]
    rw [←point]
    exact ActualWilsonPrimaryPreparation.original R d N per i opened.post live
  have pos:0<safety C i := Real.sqrt_pos.mpr (forcedPos C.path.levels i)
  obtain ⟨q,format,pay,empty,raw,_,billed⟩:=
    WilsonMeasuredMarkedPrimary.posted L hw pos valid regular forced x v C.params sec he
  rw [root] at format pay billed
  change q.remBound 0 W (safety C i) (c/θ v) at pay
  obtain ⟨receipt,_,valued⟩:=WilsonMeasuredCourseSourceGerm.original R π Γ Ψ course started live q format pay
  have eqv:(fun U=>(L.density x U).part (B.fire v)) =ᶠ[𝓝 1] q.density 0 sec W := by
    filter_upwards [Juniper.Caret.flat_flags (C.side i per) W.p.threshold W.p.threshold_pos] with U clear
    exact (healthy L hw regular x v U clear).trans (billed U clear)
  have bound : (C.labels.level d).coeffSize q.x≤2*(r+s)/θ v := by
    apply (le_div_iff₀ (hw v)).mpr
    rw [mul_comm]
    exact raw
  refine ⟨q,receipt,empty,eqv.trans valued.symm,?_,?_⟩
  · exact control_page R.makes opened live q ⟨receipt.1,rem_mono receipt.2 (le_max_left _ _)⟩
      (bound.trans (le_max_right _ _))
  · intro f u a seen same
    exact WilsonMeasuredCourseSourceGerm.primary R π Γ Ψ course started live opened.post q format pay
      u f seen (same.trans eqv)

end YM.Integration.WilsonMeasuredFullPrimary
end

