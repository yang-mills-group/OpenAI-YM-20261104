import YM.Integration.WilsonOriginalNullPlacedJointCenter
import YM.Integration.WilsonOriginalNullPlacedCalibration

/-! Convert only the measured sum of the two local coordinates into a
translated, inverse-calibrated Wilson column on the canonical physical
carrier. Large separate coordinates do not enter the regular or hard fee. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalNullPlacedJointRepair
open Function Filter MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Relay
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext Repeat Legato Graces Roost Org Push.Local
open scoped Classical BigOperators

variable {G:Gauge} (R:Run G) (d N p i:ℕ)
local notation "C₀" => R.family
local notation "F₀" => (C₀).labels.level d
local notation "S₀" => (C₀).localSection d
local notation "P₀" => (C₀).path.rep N p i
local notation "Q₀" => store C₀ d p i

theorem original (live:i ≤ N) (home:Opened C₀ d i p) (o:Site ((C₀).side i p))
    (W:Rep G ((C₀).side i p)) (same:W.p=(P₀).p) (quiet:∀ U,W.eval U=(P₀).eval U)
    (h k:Q₀) {κ B D:ℝ} (hf:h.Format o (C₀).params W) (hp:h.remBound o W κ B)
    (kf:k.Format o (C₀).params P₀) (kp:k.remBound o P₀ (safety C₀ i) D) :
    let α:=projection F₀ (C₀).params W.p.threshold o h
    let β:=projection F₀ (C₀).params (P₀).p.threshold o k
    let v:=WilsonMeasuredSectionCorrection.subtract F₀ h α
    let x:=(fitting d N p i R.makes home live).symm (α+β)
    let Y:=Drift.stamp o (Tour.placard C₀ R.makes N p live o) (((C₀).factory d N p).entries i x)
    let e:=2*stock C₀ i*(F₀).coeffSize (α+β)
    ∃ w:Q₀, v.Format o (C₀).params W ∧ v.remBound o W κ B ∧ projection F₀ (C₀).params W.p.threshold o v=0 ∧
      w.Format o (C₀).params P₀ ∧ w.remBound o P₀ (safety C₀ i) (D+e) ∧ projection F₀ (C₀).params (P₀).p.threshold o w=0 ∧
      Y.Format o (C₀).params P₀ ∧ Y.remBound o P₀ (safety C₀ i) e ∧ projection F₀ (C₀).params (P₀).p.threshold o Y=α+β ∧
      Y.density o S₀ P₀=((calValues (C:=C₀) d N p i x)∘translate o) ∧
      h.density o S₀ W+k.density o S₀ P₀=v.density o S₀ W+w.density o S₀ P₀+Y.density o S₀ P₀ := by
  intro α β v x Y e
  let t:=WilsonMeasuredSectionCorrection.subtract F₀ k β
  obtain ⟨vf,vp,vn,tf,tp,tn,field⟩:=WilsonOriginalNullPlacedJointCenter.original F₀ (C₀).params S₀ o W P₀ same quiet h k hf hp kf kp
  obtain ⟨z,zf,zp,zn,yf,yp,yn,aligned,shifted⟩:=WilsonOriginalNullPlacedCalibration.original C₀ R.makes d N p i home live o (α+β)
  have dims:=dimensions d N p i R.makes home.post live
  have together:=presentation tf tp zf zp
  have law:=(R.makes.wilson.represents N p i live).good
  have join:(beside t z).density o S₀ P₀=t.density o S₀ P₀+z.density o S₀ P₀:=plus law tp zp S₀
  have split:(primary o (α+β)).density o S₀ P₀=z.density o S₀ P₀+Y.density o S₀ P₀:=aligned
  refine ⟨beside t z,vf,vp,vn,together.1,together.2,?_,yf,yp,yn,shifted,?_⟩
  · rw [add_projection d t z tf zf dims.1 dims.2 ⟨_,_,tp⟩ ⟨_,_,zp⟩,tn,zn,zero_add]
  · calc
      _=v.density o S₀ W+t.density o S₀ P₀+(primary o (α+β)).density o S₀ P₀:=field
      _=_:=by rw [split,join];abel

end YM.Integration.WilsonOriginalNullPlacedJointRepair
