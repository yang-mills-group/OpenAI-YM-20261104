import YM.Integration.WilsonOriginalFiledSuccessorIncome

/-! Bounds and measurability of the two actual unmasked compact prints and
the measured old regular change, at the two programmes' own source radii. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalBetweenFiledPrints
open Function Finset MeasureTheory Lattice RG Wilson Marker Multi QuadraticLocal Ac
open Push Push.Local Push.AbsoluteSums Source Labels
open WilsonRootedKioskOccupiedSlip WilsonOriginalFlatFiledMask WilsonCenteredCompleteGallery
open Comparison.RG02.Cumulants WilsonCapturedPrimarySoftPartition
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}{V X X' ι ι' μ:Type}[DecidableEq V][Fintype V]{J:Census V}
   {P:Rep G n}{p':BudgetPoint}{o o':V→Site n}

theorem ordinary [Countable ι] {p:BudgetPoint} (L:Lamps X ι G p o J)(w:V→ℝ)(hw:∀a,0<w a)
    {α E:ℝ}(width:0 ≤ α)(paid:L.Paid w p.B α E)(x:X)(s:J.Mode):
    Measurable (fun U=>(Poly.pass (L.log x U)).part s):=by
  have zero (U:Config G n):(L.log x U).part J.quiet=0:=L.quiet_of_hasSum x U (paid.sums width hw x U)
  simp_rw [show ∀U:Config G n,(Poly.pass (L.log x U)).part s=∑q∈shards J s,∏t∈q.val,(L.log x U).part t.val
    from fun U=>YM.RG02.Marks.pass_partition (zero U) s]
  exact Finset.measurable_sum _ fun q _=>Finset.measurable_prod _ fun t _=>
    WilsonPhysicalMarkedDefect.PrescribedInput.measurable L hw width paid t.val x

omit [Fintype V] in
private theorem unary [Countable ι] {p:BudgetPoint}(L:Lamps X ι G p o J)(w:V→ℝ)(hw:∀a,0<w a)
    {α C:ℝ}(width:0 ≤ α)(income:Gross L w p.B α C)(x:X)(U:Config G n)(t:Hot J):
    ‖(bare L x U).part t.val‖ ≤ (Poly.toll w t.val)⁻¹*C:=by
  obtain ⟨v,hv⟩:=t.property
  rw [←mul_le_mul_iff_right₀ (Poly.worth hw t.val),←mul_assoc,mul_inv_cancel₀ (Poly.worth hw t.val).ne',one_mul]
  exact WilsonReceivedWholeFieldMask.whole L hw width income x U t.val v hv

theorem original [Countable ι][Countable ι'][Countable μ](L:Lamps X ι G P.p o J)
    (old:Lamps X μ G P.p o J)(H:Hard X P.p P.activities.forced P.activities.K o J)
    (next:Lamps X' ι' G p' o' J)(w w':V→ℝ)(hw:∀a,0<w a)(hw':∀a,0<w' a)
    {α E C rent α' C' W W' M:ℝ}(width:0 ≤ α)(width':0 ≤ α')
    (paid:L.Paid w P.p.B α E)(gross:Gross L w P.p.B α C)(refund:old.Paid w P.p.B α rent)
    (sold:Gross next w' p'.B α' C')(x:X)(z:X')(s:J.Mode)(cp:0 ≤ C)(np:0 ≤ C')
    (inlet:∀t:Hot J,t.val.val⊆s.val→(Poly.toll w t.val)⁻¹ ≤ W)
    (outlet:∀t:Hot J,t.val.val⊆s.val→(Poly.toll w' t.val)⁻¹ ≤ W')
    (price:W*C ≤ M ∧ W'*C' ≤ M):
    (∀U,(bare next z U).part J.quiet=0) ∧
      Measurable (fun U=>(Poly.pass (bare L x U)).part s+
        (soft (posted L old H) x s U-(Poly.pass (L.log x U)).part s)-(Poly.pass (bare next z U)).part s) ∧
      ∀U (t:Hot J),t.val.val⊆s.val→‖(bare L x U).part t.val‖ ≤ M ∧ ‖(bare next z U).part t.val‖ ≤ M:=by
  constructor
  · exact WilsonRootedKioskCompleteFiling.quiet next hw' width' sold z
  constructor
  · exact ((WilsonReceivedWholeFieldHot.borel L hw width gross x s).add
      ((ordinary (L.join old) w hw width (Lamps.joinPaid paid refund) x s).sub
        (ordinary L w hw width paid x s))).sub (WilsonReceivedWholeFieldHot.borel next hw' width' sold z s)
  · intro U t ht
    exact ⟨(unary L w hw width gross x U t).trans ((mul_le_mul_of_nonneg_right (inlet t ht) cp).trans price.1),
      (unary next w' hw' width' sold z U t).trans ((mul_le_mul_of_nonneg_right (outlet t ht) np).trans price.2)⟩

end YM.Integration.WilsonOriginalBetweenFiledPrints
