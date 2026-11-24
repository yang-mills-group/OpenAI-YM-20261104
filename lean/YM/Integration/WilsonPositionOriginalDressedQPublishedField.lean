import YM.Integration.WilsonPositionOriginalDressedQLiteralLamp

/-! An actual published, unmasked row is a bounded Borel field with the
quoted rooted cost, including on the genuinely failed configurations. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionOriginalDressedQPublishedField
open Lattice RG Wilson Marker Cells QuadraticLocal MeasureTheory
open WilsonRootedKioskOccupiedSlip
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}{P:BudgetPoint}{V T I:Type}[DecidableEq V]
  {o:V→Site n}{Γ:Census V}(L:Lamps T I G P o Γ){B:ℕ}{w:V→ℝ}{a c:ℝ}

theorem charged (hw:∀v,0<w v)(ha:0 ≤ a)(paid:Gross L w B a c)
    (s:Γ.Mode)(v:V)(reach:v∈s.val)(t:T)(U:Config G n):
    ‖(bare L t U).part s‖ ≤ (Poly.toll w s)⁻¹*c:=by
  have priced:=WilsonPositionOriginalDressedQLiteralLamp.tail L B 0 hw ha paid s v reach t U
  simpa [WilsonPositionOriginalDressedQLiteralLamp.short,WilsonPositionOriginalDressedQLampColumn.portion] using priced

theorem entire [Countable I](hw:∀v,0<w v)(ha:0 ≤ a)(paid:Gross L w B a c)
    (s:Γ.Mode)(v:V)(reach:v∈s.val)(t:T):Envelope (fun U=>(bare L t U).part s):=by
  classical
  refine ⟨?_,_,charged L hw ha paid s v reach t⟩
  have val (U:Config G n):(bare L t U).part s=
      ∑'i,(Poly.send (L.mode i) (L.nominal t i U)).part s:=
    Poly.share (WilsonRootedKioskCompleteFiling.sums L hw ha paid t U).1 s
  simp_rw [val]
  apply Measurable.tsum; intro i
  by_cases same:s=L.mode i
  · simpa [Poly.part_send,same] using (L.legal t i).borel
  · simp [Poly.part_send,same]

end YM.Integration.WilsonPositionOriginalDressedQPublishedField
