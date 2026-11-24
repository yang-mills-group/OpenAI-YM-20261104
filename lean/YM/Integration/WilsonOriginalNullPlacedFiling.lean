import YM.Integration.WilsonOriginalNullPlacedCalibration
import YM.Trace.Physicalv2.GermSplit

/-! Project the complete original coefficient once at its actual site.
The fitted survivor and the null term both keep the canonical Wilson
carrier's numerical regular and compulsory inventory. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalNullPlacedFiling
open Function Filter MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Relay
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext Repeat Legato Graces Roost Org Push.Local
open scoped Classical BigOperators

variable {G:Gauge} (C:Family G) (H:C.Makes) (d N p i:ℕ)
local notation "F₀" => C.labels.level d
local notation "S₀" => C.localSection d
local notation "P₀" => C.path.rep N p i
local notation "Q₀" => store C d p i

theorem original (home:Opened C d i p) (live:i≤N) (o:Site (C.side i p)) (q:Q₀) (B:ℝ)
    (form:q.Format o C.params P₀) (fund:q.remBound o P₀ (safety C i) B) (head:(F₀).coeffSize q.x≤B) :
    let π:=projection F₀ C.params (P₀).p.threshold o q
    let x:=(fitting d N p i H home live).symm π
    let Y:=Drift.stamp o (Tour.placard C H N p live o) ((C.factory d N p).entries i x)
    ∃ v:Q₀, v.Format o C.params P₀ ∧ v.remBound o P₀ (safety C i) ((1+4*stock C i)*B) ∧
      projection F₀ C.params (P₀).p.threshold o v=0 ∧ mCost C d N p i x≤2*B ∧
      projection F₀ C.params (P₀).p.threshold o Y=π ∧
      q.density o S₀ P₀=v.density o S₀ P₀+Y.density o S₀ P₀ ∧
      Y.density o S₀ P₀=(calValues (C:=C) d N p i x) ∘ Lattice.translate o := by
  intro π x Y
  let move:=Tour.placard C H N p live (-o)
  let centered:=Drift.stamp (-o) move q
  have resp:reads (C:=C) d N p i centered B:=by
    refine ⟨?_,?_⟩
    · simpa only [add_neg_cancel] using Drift.stamp_format (-o) move q form
    · simpa only [add_neg_cancel] using Drift.stamp_rem (-o) move q fund
  have vac:=(H.wilson.represents N p i live).vac
  have same:page (C:=C) d p i centered=π:=by
    have hg:=WilsonOriginalNullRelocation.page F₀ C.params (P₀).p.threshold o (-o) move q
    rw [add_neg_cancel] at hg
    change projection F₀ C.params ((C.path.levels.budget i).threshold) 0 centered=projection F₀ C.params (P₀).p.threshold o q
    rw [←vac];exact hg
  have bound:=(control_page H home live centered resp head)
  rw [same] at bound
  obtain ⟨_,_,_,_,yf,yp,ypi,_,raw⟩:=WilsonOriginalNullPlacedCalibration.original C H d N p i home live o π
  obtain ⟨dw,pw⟩:=dimensions d N p i H home.post live
  obtain ⟨v,vf,vp,vn,actual⟩:=WilsonOriginalNullColumnSplit.original C.params S₀ P₀ o q Y
    (H.wilson.represents N p i live).good dw pw
    form fund yf yp ypi
  have f:fitting d N p i H home live x=π:=(fitting d N p i H home live).apply_symm_apply π
  have mass:mCost C d N p i x=(F₀).coeffSize π:=
    congrArg (F₀).coeffSize ((fitting_apply (C:=C) d N p i H home live x).symm.trans f)
  refine ⟨v,vf,rem_mono vp ?_,vn,mass.trans_le bound,ypi,funext actual,raw⟩
  have paid:=mul_le_mul_of_nonneg_left bound (show 0≤2*stock C i from
    mul_nonneg zero_le_two (zero_le_one.trans (stage C i).columns_ge))
  linarith

end YM.Integration.WilsonOriginalNullPlacedFiling
