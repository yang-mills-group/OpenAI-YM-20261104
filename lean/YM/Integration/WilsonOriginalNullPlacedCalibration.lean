import YM.Integration.WilsonOriginalNullRelocation

/-! The true calibrated Wilson survivor can be installed at every physical
receiving root, using the existing numerical forced permutation on that
same canonical Wilson representation. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalNullPlacedCalibration
open Function Filter MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Relay
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext Repeat Legato Graces Roost Org Push.Local
open scoped Classical BigOperators

variable {G:Gauge} (C:Family G) (H:C.Makes) (d N p i:ℕ)
local notation "F₀" => C.labels.level d
local notation "S₀" => C.localSection d
local notation "P₀" => C.path.rep N p i
local notation "Q₀" => store C d p i

theorem original (home:Opened C d i p) (live:i ≤ N) (o:Site (C.side i p)) (α:C.label d) :
    let x:=(fitting d N p i H home live).symm α
    let move:=Tour.placard C H N p live o
    let Y:=Drift.stamp o move ((C.factory d N p).entries i x)
    let salary:=2*stock C i*(F₀).coeffSize α
    ∃ w:Q₀, w.Format o C.params P₀ ∧ w.remBound o P₀ (safety C i) salary ∧
      projection F₀ C.params (P₀).p.threshold o w=0 ∧ Y.Format o C.params P₀ ∧
      Y.remBound o P₀ (safety C i) salary ∧ projection F₀ C.params (P₀).p.threshold o Y=α ∧
      (primary o α).density o S₀ P₀=w.density o S₀ P₀+Y.density o S₀ P₀ ∧
      Y.density o S₀ P₀=(calValues (C:=C) d N p i x)∘translate o := by
  intro x move Y salary
  obtain ⟨w,wr,wn,field⟩:=WilsonOriginalNullCalibrated.aligned C d N p i H home live α
  let q:Q₀:=(C.factory d N p).entries i x
  have fx:fitting d N p i H home live x=α:=(fitting d N p i H home live).apply_symm_apply α
  have qr:reads (C:=C) d N p i q salary:=by
    have quote:=graph_cost d N p i H home live x
    rw [fx] at quote
    exact quote
  have vac:=(H.wilson.represents N p i live).vac
  have qw:projection F₀ C.params (P₀).p.threshold 0 w=0:=by rw [vac];exact wn
  have qh:projection F₀ C.params (P₀).p.threshold 0 q=α:=by
    rw [vac];exact (fitting_apply (C:=C) d N p i H home live x).symm.trans fx
  have project (a:Q₀):projection F₀ C.params (P₀).p.threshold o (Drift.stamp o move a) =
      projection F₀ C.params (P₀).p.threshold 0 a:=by
    simpa only [zero_add] using WilsonOriginalNullRelocation.page F₀ C.params (P₀).p.threshold 0 o move a
  have actual (a:Q₀):(Drift.stamp o move a).density o S₀ P₀=(a.density 0 S₀ P₀)∘translate o:=by
    simpa only [zero_add,Function.comp_def] using WilsonOriginalNullRelocation.registered C H d N p i live 0 o a
  refine ⟨Drift.stamp o move w,?_,?_,(project w).trans qw,?_,?_,(project q).trans qh,?_,actual q⟩
  · simpa only [zero_add] using Drift.stamp_format o move w wr.1
  · simpa only [zero_add] using Drift.stamp_rem o move w wr.2
  · simpa only [zero_add] using Drift.stamp_format o move q qr.1
  · simpa only [zero_add] using Drift.stamp_rem o move q qr.2
  · have prim:=actual (primary 0 α)
    rw [WilsonOriginalNullRelocation.center F₀ 0 o move α,zero_add] at prim
    rw [prim,actual w,actual q]
    funext U
    exact congrFun field (Lattice.translate o U)

end YM.Integration.WilsonOriginalNullPlacedCalibration
