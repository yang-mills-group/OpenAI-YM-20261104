import YM.Integration.WilsonMacroscopicRichCapturedChildTape

/-! Explicit filing of a physical product minus its chosen counterterm. The
reference may be the canonical report at a different, fixed lower date. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichChildRemainder
open Lattice Wilson RG Source Labels RG16.Literal Trace.Physical.GermGraph
open Extra.Histories Extra.Histories.Relay
open scoped BigOperators Classical
open private registered_credit from YM.Integration.WilsonMacroscopicRichChildRegistration
open private plus_value from YM.Trace.Physicalv2.GermStep
variable {G : Gauge} (C : Family G) (H : C.Makes) {d n N p : ℕ}

private theorem subtract (live : n≤N) (Y K : Cut C N p) (cY : Continuous Y) (cK : Continuous K) :
    credit C N p d (Y-K) n live=credit C N p d Y n live-credit C N p d K n live := by
  let A : Fin 2 → Cut C N p := ![Y,K]
  let w : Fin 2 → ℂ := ![1,-1]
  have continuous (j : Fin 2) : Continuous (A j) := by
    fin_cases j
    · exact cY
    · exact cK
  simpa [A,w,Fin.sum_univ_two,sub_eq_add_neg] using
    (IntrinsicProductLinearity.credit_sum C N p d n live w A continuous)

theorem original (opened : Opened C d n p) (live : n≤N)
    (Y : Cut C N p) (cY : Continuous Y) (v : C.label d) (q : store C d p n) {e : ℝ}
    (fee : reads d N p n q e) (issued : credit C N p d Y n live=value (C:=C) d N p n q) :
    let fit := fitting d N p n H opened live
    let A := Y-C.O N p ((C.factory d N p).terminal v) 0
    let total := beside q ((C.factory d N p).entries n (-v))
    reads d N p n total (e+2*stock C n*(C.labels.level d).coeffSize (fit v)) ∧
    credit C N p d A n live=value (C:=C) d N p n total ∧
    page (C:=C) d p n total=page (C:=C) d p n q-fit v := by
  intro fit A total
  have price := graph_cost (C:=C) d N p n H opened live (-v)
  have sign : (C.labels.level d).coeffSize (fitting d N p n H opened live (-v)) =
      (C.labels.level d).coeffSize (fit v) := by
    rw [map_neg]
    simp [Frame.coeffSize,fit]
  rw [sign] at price
  refine ⟨presentation fee.1 fee.2 price.1 price.2,?_,?_⟩
  · have entry:=registered_credit C H (p:=p) ((C.factory d N p).terminal v) opened.post live
    rw [LinearEquiv.symm_apply_apply] at entry
    have negative : calValues (C:=C) d N p n (-v) = -calValues (C:=C) d N p n v := by
      apply eq_neg_of_add_eq_zero_left
      rw [←cal_add d N p n H opened.post live,neg_add_cancel,zero_cal d N p n H opened.post live]
    change credit C N p d (Y-_) n live=value (C:=C) d N p n (beside q _)
    rw [subtract C live _ _ cY (C.continuousO ..),issued,entry,
      plus_value d N p n q _ H live fee price]
    change _ = value (C:=C) d N p n q+calValues (C:=C) d N p n (-v)
    rw [negative,sub_eq_add_neg]
  · rw [show page (C:=C) d p n total=_ from addPage d N p n q _ H opened.post live fee price]
    change _+fit (-v)=_
    rw [map_neg,sub_eq_add_neg]

end YM.Integration.WilsonMacroscopicRichChildRemainder

