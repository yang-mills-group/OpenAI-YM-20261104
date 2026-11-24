import YM.Integration.WilsonOriginalNullPlacedJointRepair
import YM.Integration.WilsonOriginalNullPlacedJointCenter
import YM.Integration.WilsonOriginalNullPlacedCalibration

/-! Convert only the measured sum of the two local coordinates into a
translated, inverse-calibrated Wilson column on the canonical physical
carrier. Large separate coordinates do not enter the regular or hard fee. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalNullBareSplit
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
    (W:Rep G ((C₀).side i p)) (same:W.p=(P₀).p) (quiet:∀ V,W.eval V=(P₀).eval V)
    (h:Q₀) {B J:ℝ} (hf:h.Format o (C₀).params W)
    (hp:h.remBound o W (safety C₀ i) B)
    (mass:(F₀).coeffSize (projection F₀ (C₀).params W.p.threshold o h) ≤ J):
    ∃ (x:(C₀).label d) (v w:Q₀),
      v.Format o (C₀).params W ∧ v.remBound o W (safety C₀ i) B ∧
      w.Format o (C₀).params P₀ ∧ w.remBound o P₀ (safety C₀ i) (2*stock C₀ i*J) ∧
      projection F₀ (C₀).params W.p.threshold o v=0 ∧
      projection F₀ (C₀).params (P₀).p.threshold o w=0 ∧
      h.density o S₀ W=((calValues (C:=C₀) d N p i x) ∘ translate o)+
        (v.density o S₀ W+w.density o S₀ P₀) := by
  let k:Q₀:=primary o 0
  have kf:k.Format o (C₀).params P₀:=primary_format 0
  have pos:0<safety C₀ i:=Real.sqrt_pos.mpr (Real.exp_pos _)
  have kp:k.remBound o P₀ (safety C₀ i) 0:=primary_rem (R:=P₀) (o:=o) (0:(F₀).Coeff) pos
  have dim:=dimensions d N p i R.makes home.post live
  have kg:projection F₀ (C₀).params (P₀).p.threshold o k=0:=
    WilsonOriginalNullCalibrated.raw_page F₀ (C₀).params P₀ o 0 dim.1 dim.2
  have kz:k.density o S₀ P₀=0:=by
    funext V
    simp only [k,primary_density,map_zero,mul_zero,Pi.zero_apply]
  have purchased:=WilsonOriginalNullPlacedJointRepair.original R d N p i live home o W same quiet h k hf hp kf kp
  dsimp only at purchased
  simp only [kg,add_zero,zero_add,kz] at purchased
  obtain ⟨w,vf,vp,vn,wf,wp,wn,_,_,_,yval,eq⟩:=purchased
  let α:=projection F₀ (C₀).params W.p.threshold o h
  let x:=(fitting d N p i R.makes home live).symm α
  let v:=WilsonMeasuredSectionCorrection.subtract F₀ h α
  refine ⟨x,v,w,vf,vp,wf,rem_mono wp ?_,vn,wn,?_⟩
  · apply mul_le_mul_of_nonneg_left mass
    change (0:ℝ) ≤ 2*((C₀).path.levels.params i).columns
    linarith only [((C₀).path.levels.params i).columns_ge]
  · rw [yval] at eq
    exact eq.trans (add_comm _ _)
end YM.Integration.WilsonOriginalNullBareSplit
