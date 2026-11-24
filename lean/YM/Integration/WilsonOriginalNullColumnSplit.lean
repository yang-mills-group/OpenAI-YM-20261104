import YM.Integration.WilsonOriginalNullProjectedPrice
import YM.Integration.WilsonOriginalNullPhysicalReturn
import YM.Extra.SOURCE_HISTORIES.Pencil

/-! Subtract any normalized, actually registered section at its own measured
incoming coordinate. The counted regular and original hard arrays remain on
the same lower carrier. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalNullColumnSplit
open Function Filter MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Relay
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge} {d:ℕ} {F:Frame G d} {n:Side}
    (A:Hol G) (S:SectionData F) (W:Rep G n) (o:Site n)

theorem scale_page (Q:Coefficient F n) (c:ℂ) {κ b:ℝ}
    (dw:d ≤ W.p.order) (pw:d ≤ W.p.power) (form:Q.Format o A W) (paid:Q.remBound o W κ b) :
    projection F A W.p.threshold o (stretch c Q)=c • projection F A W.p.threshold o Q := by
  let m(a:ℂ):=stretch a Q
  have one : m 1=Q := by simp only [m,stretch,one_smul]
  have lin : IsLinearMap ℂ (fun a:ℂ=>(m a).x) ∧ IsLinearMap ℂ (fun a:ℂ=>(m a).regular) :=
    ⟨⟨fun a b=>add_smul ..,fun a b=>smul_assoc ..⟩,⟨fun a b=>add_smul ..,fun a b=>smul_assoc ..⟩⟩
  have hp:=Germ.linear_projection F A (o:=o) m dw pw
    (fun a=>stretch_format a form) (fun a=>⟨_,_,stretch_rem a paid⟩) lin
  simpa only [smul_eq_mul,mul_one,one] using hp.map_smul c 1

/-- Both operands have their own true regular and forced budgets. The equality
also holds on rough fields sharing a lower original owner. -/
theorem original (P Y:Coefficient F n) {κ b e σ C Λ δ w:ℝ} (law:W.Lawful σ C Λ δ w)
    (dw:d ≤ W.p.order) (pw:d ≤ W.p.power) (form:P.Format o A W) (paid:P.remBound o W κ b)
    (sForm:Y.Format o A W) (sPaid:Y.remBound o W κ e)
    (registered : projection F A W.p.threshold o Y=projection F A W.p.threshold o P) :
    ∃ z:Coefficient F n,z.Format o A W ∧ z.remBound o W κ (b+e) ∧
      projection F A W.p.threshold o z=0 ∧
      ∀ U,P.density o S W U=z.density o S W U+Y.density o S W U := by
  let shadow:=stretch (-1:ℂ) Y
  have shaped : shadow.Format o A W:=stretch_format _ sForm
  have earned : shadow.remBound o W κ e:=by simpa [shadow] using stretch_rem (-1:ℂ) sPaid
  obtain ⟨ready,charged⟩:=presentation form paid shaped earned
  refine ⟨beside P shadow,ready,charged,?_,?_⟩
  · rw [GermGraph.add_projection d P shadow form shaped dw pw ⟨_,_,paid⟩ ⟨_,_,earned⟩]
    rw [show projection F A W.p.threshold o shadow=(-1:ℂ) • projection F A W.p.threshold o Y from
      scale_page A W o Y _ dw pw sForm sPaid,registered,neg_one_smul,add_neg_cancel]
  · intro U
    have h:=congrFun (plus law paid earned S) U
    change (beside P shadow).density o S W U=P.density o S W U+shadow.density o S W U at h
    rw [h,show shadow.density o S W U=(-1:ℂ)*Y.density o S W U from stretch_density S W o (-1) Y U];ring

end YM.Integration.WilsonOriginalNullColumnSplit
