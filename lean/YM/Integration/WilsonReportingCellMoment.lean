import YM.Integration.WilsonReportingCellProfile
import YM.RG02.Actual.Selected
import YM.OPE.Therm.Law

/-! The normalized physical one-point function on the entire selected
spine at its real reporting date and with its original affine test. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingCellMoment
open Function Filter Finset MeasureTheory Lattice Wilson RG Source RG12 Extra.Histories
open Trace.Physical RG05Readout Address Native WilsonReportingCellMotion WilsonReportingCellIntegral
open scoped Classical
variable {G:Gauge} {C:Family G} {d m N per b:ℕ}
variable {D:Rail C} {B:ℕ→ℕ→ℝ} {V:Sight C d per} {U:Emblems C d}

private theorem probability (h:C.Makes) (live:m ≤ N) (F:Goods G (C.side m per)) :
    (∫ X,Juniper.Caret.ratio (C.path.rep N per m) F X ∂OPE.Therm.scene C.path N per m) =
    total F/(partition G (C.side N per) (C.path.β N per N):ℂ) := by
  rw [OPE.Therm.violet h.wilson live]
  have cancel (X:Config G (C.side m per)):((C.path.rep N per m).eval X:ℂ)*
      Juniper.Caret.ratio (C.path.rep N per m) F X=F X := by
    have pos:((C.path.rep N per m).eval X:ℂ)≠0:=
      Complex.ofReal_ne_zero.mpr (RG02.Actual.eval_pos h.wilson live X).ne'
    change _ * (F X / _) = F X
    field_simp [pos]
  simp only [cancel,total]

def read (t:Letter d) (x:C.label (kept t)) (m N per:ℕ) (V:Sight C d per) (U:Emblems C d)
    (φ:Body):ℂ :=
  let v:=(C.factory (kept t) N per).terminal.symm x
  let y:=Many.point U (chunk t v) N m
  ∫ X,Juniper.Caret.ratio (C.path.rep N per m) (pulseOut (V m y) φ) X ∂OPE.Therm.scene C.path N per m

theorem original (h:C.Makes) (spine:Spine D B h b per d N V U)
    (starts:∀e ≤ d,C.ref e ≤ N) (t:Letter d) (x:C.label (kept t)) (aged:C.ref (kept t) ≤ m)
    (beginning:b ≤ m) (live:m ≤ N) (φ:Body) :
    read t x m N per V U φ =
    WilsonReportingCellField.profile C per m (depth t) (N-m) (readJ t 0) φ *
      ((C.S.a m:ℂ)^(kept t)*moment (C.path.β N per N) (C.O N per x 0)) := by
  obtain ⟨q,rfl⟩:=Nat.exists_eq_add_of_le live
  let T:=C.factory (kept t) (m+q) per
  let v:=T.terminal.symm x
  let p:=(partition G (C.side (m+q) per) (C.path.β (m+q) per (m+q)):ℂ)
  have p0:p≠0:=Complex.ofReal_ne_zero.mpr (partition_pos _).ne'
  have actual:=WilsonReportingCellRoute.bare h spine beginning (chunk t v)
  rw [WilsonReportingBareCell.bare h starts] at actual
  have law:=TransferData.integral_marked h.wilson (h.calibrated _ (m+q) per (aged.trans live))
    x m aged live
  have stock:total (row C t v (m+q) per m)=(C.S.a m:ℂ)^(kept t)*p*
      moment (C.path.β (m+q) per (m+q)) (C.O (m+q) per x 0) := law
  unfold read
  rw [probability h live]
  change total (pulseOut (V m (Many.point U (chunk t v) (m+q) m)) φ)/p=_
  rw [←actual,WilsonReportingCellField.integral h t v aged q le_rfl,stock,Nat.add_sub_cancel_left]
  field_simp [p0]

theorem paid (h:C.Makes) (spine:Spine D B h b per d N V U)
    (starts:∀e ≤ d,C.ref e ≤ N) (t:Letter d) (x:C.label (kept t)) (aged:C.ref (kept t) ≤ m)
    (beginning:b ≤ m) (live:m ≤ N) (φ:Body) (c:ℝ) (cost:Cap (d+2) φ c) :
    ‖read t x m N per V U φ‖ ≤ pulseFee d*c *
      ‖(C.S.a m:ℂ)^(kept t)*moment (C.path.β N per N) (C.O N per x 0)‖ := by
  rw [original h spine starts t x aged beginning live,norm_mul]
  exact mul_le_mul_of_nonneg_right
    ((WilsonReportingCellProfile.original t (N-m)).bound φ _ (fun _ hx=>fees d t hx cost))
    (norm_nonneg _)

theorem diagonal (h:C.Makes) (spine:Spine D B h b per d N V U)
    (starts:∀e ≤ d,C.ref e ≤ N) (t i:Letter d) (x:C.label (kept t)) (aged:C.ref (kept t) ≤ m)
    (beginning:b ≤ m) (live:m ≤ N) (low:depth i ≤ depth t) :
    read t x m N per V U (line i) = if t=i then
      (C.S.a m:ℂ)^(kept t)*moment (C.path.β N per N) (C.O N per x 0) else 0 := by
  rw [original h spine starts t x aged beginning live,
    (WilsonReportingCellProfile.original t (N-m)).constant (line i) _ (fun y _=>sliceC t i y low)]
  split <;> simp

end YM.Integration.WilsonReportingCellMoment
