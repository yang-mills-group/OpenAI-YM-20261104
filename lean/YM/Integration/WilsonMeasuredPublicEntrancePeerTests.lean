import YM.Integration.WilsonMeasuredPublicEntranceOwnerIntegrable
import YM.Integration.WilsonMeasuredPublicEntranceFiredTail
import YM.Integration.WilsonFirstReceivedGalleryRegular
import YM.Integration.WilsonMeasuredCompanionTest

/-! Measurability and genuine full-field bounds for the two sorts of
spectators of an occupied trial, on their original finite Wilson film. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntrancePeerTests
open Function Finset MeasureTheory Lattice Wilson RG Labels Source Marker QuadraticLocal
open Push.Local Push.AbsoluteSums PhysicalNext PhysicalNext.Repeat Legato Extra.Histories
open WilsonMeasuredPublicEntranceOrder WilsonThermometerUnitFilingFieldRange WilsonMeasuredCoefficientTransport
open WilsonPhysicalMarkedDefect.RegularProjection
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){f p:ℕ}{d:ℕ}{V T I:Type}[DecidableEq V]{J:Census V}
local notation "cfg" => Config G (R.family.side f p)
variable (W:Rep G (R.family.side f p))(o:V → Site (R.family.side f p)) (v:V)
variable (q:Coefficient (R.family.labels.level d) (R.family.side f p))
  {κ B:ℝ}(fit:q.Format (o v) R.family.params W)(paid:q.remBound (o v) W κ B)

omit [DecidableEq V] in
include paid fit in
theorem canonical:BoundedAt R.family (q.exponentialEntry (o v) (R.family.localSection d) W):=by
  refine ⟨?_,_,point R d W q (o v) paid⟩
  have meas:Measurable (q.exponentialEntry (o v) (R.family.localSection d) W):=
    (measurable_const.add (masked_measurable _ _ _ ((R.family.localSection d).continuous_places ..).measurable)).add
      (Measurable.tsum (fun i=>masked_measurable _ _ _ (fit.smooth i).borel))
  exact meas.aestronglyMeasurable

theorem trial [Countable I](E:Lamps T I G W.p o J)(x:T)(w:V→ℝ)(wp:∀i,0<w i)
    {a A:ℝ}(ap:0≤a)(fee:E.Paid w W.p.B a A):BoundedAt R.family (fun U=>(E.log x U).part (J.fire v)) ∧
    ∀U,‖(E.log x U).part (J.fire v)‖≤A/w v:=by
  have logs:Measurable (E.log x):=by
    apply Measurable.tsum (f:=fun i U=>E.frame i x U)
    intro i
    apply (Overlay.Bands.sends _).measurable.comp
    unfold Lamps.light
    split
    · exact (E.legal x i).borel
    · exact masked_measurable _ _ _ (E.legal x i).borel
  have cap(U):‖(E.log x U).part (J.fire v)‖≤A/w v:=by
    have cash:=WilsonFirstReceivedGalleryRegular.occupied E fee ap wp x U (J.fire v) v (mem_singleton_self _)
    rw [Poly.solo_toll] at cash
    exact (le_div_iff₀ (wp v)).mpr ((mul_comm _ _).le.trans cash)
  exact ⟨⟨((Poly.get _).measurable.comp logs).aestronglyMeasurable,_,cap⟩,cap⟩

omit [DecidableEq V] in
include paid fit in
theorem hard {σ c Λ δ z:ℝ}(law:W.Lawful σ c Λ δ z)(x0:q.x=0)(r0:q.regular=0):
    BoundedAt R.family (account q W):=by
  have sale:=q.envelope (R.family.localSection d) law paid fit
  have vanished(U):q.exponentialEntry (o v) (R.family.localSection d) W U=0:=by
    simp [Coefficient.exponentialEntry,Coefficient.maskedTerm,x0,r0,masked,SectionData.places,SectionData.evaluate]
  have exactField(U):account q W U=q.density (o v) (R.family.localSection d) W U:=by
    change _=(_ : ℂ)*q.exponentialEntry (o v) (R.family.localSection d) W U+_
    rw [vanished,mul_zero,zero_add]
    rfl
  rw [funext exactField]
  obtain ⟨A,dom⟩:=sale.cost
  exact ⟨sale.meas.aestronglyMeasurable,A,dom⟩

theorem dressed (h:cfg→ℂ)(hh:BoundedAt R.family h)(a:V→cfg→ℂ)(fee:∀v,BoundedAt R.family (a v))
    (s:Finset V):Integrable (fun U=>h U*∏i∈s,a i U) (prior G _):=by
  have items(t:Finset V):BoundedAt R.family (fun U=>∏i∈t,a i U):=by
    induction t using Finset.induction_on with
    | empty=>simpa only [prod_empty] using (one R.family (K:=f) (p:=p))
    | @insert i t hi ih=>simpa only [prod_insert,hi,not_false_eq_true] using times R.family (fee i) ih
  obtain ⟨me,A,bill⟩:=times R.family hh (items s)
  exact Integrable.of_bound me A (ae_of_all _ bill)

end YM.Integration.WilsonMeasuredPublicEntrancePeerTests
end
