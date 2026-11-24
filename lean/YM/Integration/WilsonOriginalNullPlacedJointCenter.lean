import YM.Integration.WilsonOriginalNullPlacedJointBalance
import YM.Integration.WilsonMeasuredSectionCorrection

/-! Remove the two measured coordinates separately on their original
inventories, then collect the local physical primaries before charging
a fee. Opposing primary coordinates cancel identically on every field. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalNullPlacedJointCenter
open Function Filter Lattice RG Wilson Extra.Histories Source Labels
open Extra.Histories.Relay Trace.Physical Trace.Physical.Germ
open WilsonMeasuredSectionCorrection
open scoped Classical BigOperators Topology
variable {G:Gauge} {d:ℕ} (F:Frame G d) (A:Hol G) (S:SectionData F)
    {n:Side} (o:Site n)

theorem remove (W:Rep G n) (q:Coefficient F n) {κ B:ℝ} (form:q.Format o A W) (paid:q.remBound o W κ B) :
    let α:=projection F A W.p.threshold o q
    let v:=subtract F q α
    v.Format o A W ∧ v.remBound o W κ B ∧ projection F A W.p.threshold o v=0 ∧
      q.density o S W=v.density o S W+(primary o α).density o S W := by
  intro α v
  refine ⟨⟨form.smooth,form.origin,form.identity_null,form.projects,form.forcing,form.carried,
    form.invariant,form.supported,form.borel⟩,paid,?_,?_⟩
  · change q.x-(q.x+∑' j,vector F A W.p.threshold o (q.regular j))+
      (∑' j,vector F A W.p.threshold o (q.regular j))=0
    abel
  · funext U
    change _=_+(primary o α).density o S W U
    rw [primary_density]
    exact all_fields F S o W q α U

theorem merge (W P:Rep G n) (same:W.p=P.p) (quiet:∀ U,W.eval U=P.eval U) (α β:F.Coeff) :
    (primary o α).density o S W+(primary o β).density o S P=(primary o (α+β)).density o S P := by
  funext U
  change (primary o α).density o S W U+(primary o β).density o S P U=(primary o (α+β)).density o S P U
  rw [primary_density,primary_density,primary_density,quiet U,map_add,mul_add]
  have sameSection:part S o W U α=part S o P U α:=by
    change α 0+RG.masked W.p.threshold (S.footprint o) (S.places (F.scaled W.p.threshold⁻¹ (F.core α)) o) U=
      α 0+RG.masked P.p.threshold (S.footprint o) (S.places (F.scaled P.p.threshold⁻¹ (F.core α)) o) U
    rw [same]
  rw [sameSection]

theorem original (W P:Rep G n) (same:W.p=P.p) (quiet:∀ U,W.eval U=P.eval U)
    (h k:Coefficient F n) {κ υ B D:ℝ} (hf:h.Format o A W) (hp:h.remBound o W κ B)
    (kf:k.Format o A P) (kp:k.remBound o P υ D) :
    let α:=projection F A W.p.threshold o h
    let β:=projection F A P.p.threshold o k
    let v:=subtract F h α
    let w:=subtract F k β
    v.Format o A W ∧ v.remBound o W κ B ∧ projection F A W.p.threshold o v=0 ∧
      w.Format o A P ∧ w.remBound o P υ D ∧ projection F A P.p.threshold o w=0 ∧
      h.density o S W+k.density o S P=v.density o S W+w.density o S P+(primary o (α+β)).density o S P := by
  intro α β v w
  obtain ⟨vf,vp,vn,first⟩:=remove F A S o W h hf hp
  obtain ⟨wf,wp,wn,second⟩:=remove F A S o P k kf kp
  refine ⟨vf,vp,vn,wf,wp,wn,?_⟩
  rw [first,second,←merge F S o W P same quiet α β]
  abel

theorem zero (W P:Rep G n) (same:W.p=P.p) (quiet:∀ U,W.eval U=P.eval U)
    (h k:Coefficient F n) {κ υ B D:ℝ} (hf:h.Format o A W) (hp:h.remBound o W κ B)
    (kf:k.Format o A P) (kp:k.remBound o P υ D)
    (null:projection F A W.p.threshold o h+projection F A P.p.threshold o k=0) :
    let v:=subtract F h (projection F A W.p.threshold o h)
    let w:=subtract F k (projection F A P.p.threshold o k)
    v.Format o A W ∧ v.remBound o W κ B ∧ projection F A W.p.threshold o v=0 ∧
      w.Format o A P ∧ w.remBound o P υ D ∧ projection F A P.p.threshold o w=0 ∧
      h.density o S W+k.density o S P=v.density o S W+w.density o S P := by
  obtain ⟨vf,vp,vn,wf,wp,wn,field⟩:=original F A S o W P same quiet h k hf hp kf kp
  have unit:(primary o (0:F.Coeff)).density o S P=0:=by
    funext U;rw [primary_density,map_zero,mul_zero];rfl
  rw [null,unit,add_zero] at field
  exact ⟨vf,vp,vn,wf,wp,wn,field⟩

end YM.Integration.WilsonOriginalNullPlacedJointCenter
