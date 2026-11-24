import YM.RG05Readout.Weave.Average
import YM.RG05Readout.Many.Ramp

/-! Compose the physical conditional pushes with the actual moving child
site and the affine change of the test before evaluating any angular jet. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingCellRoute
open Lattice Wilson RG Source Labels RG05Readout Address Native
variable {G:Gauge} {C:Family G} {m N per b d:ℕ}

def route (C:Family G) (per N d m:ℕ) :
    (q:ℕ) → (Body→Goods G (C.side (m+q) per)) → Body→Goods G (C.side m per)
  | 0,F=>F
  | q+1,F=>route C per N d m q (journey C per (m+q) N d F)

theorem along (h:C.Makes) {D:Rail C} {B:ℕ→ℕ→ℝ} {V:Sight C d per} {U:Emblems C d}
    (spine:Spine D B h b per d N V U) (beginning:b ≤ m) (x:Palette C d) (q:ℕ)
    (live:m+q ≤ N) :
    route C per N d m q (pulseOut (V (m+q) (Many.point U x N (m+q)))) =
      pulseOut (V m (Many.point U x N m)) := by
  induction q with
  | zero => rfl
  | succ q ih =>
    have step : pulseOut (V (m+q) (Many.point U x N (m+q))) =
        journey C per (m+q) N d (pulseOut (V (m+q+1) (Many.point U x N (m+q+1)))) := by
      rw [← Many.nearpoints U x (m+q)]
      funext f
      exact travels h spine (by omega) (by omega) f _
    exact (congrArg (route C per N d m q) step.symm).trans (ih (by omega))

theorem bare (h:C.Makes) {D:Rail C} {B:ℕ→ℕ→ℝ} {V:Sight C d per} {U:Emblems C d}
    (spine:Spine D B h b per d (m+N) V U) (beginning:b ≤ m) (x:Palette C d) :
    route C per (m+N) d m N (pulseOut (basisTop C d (m+N) per x)) =
      pulseOut (V m (Many.point U x (m+N) m)) := by
  have payment:=along h spine beginning x N (le_refl _)
  rw [Many.point_here,spine.starts] at payment
  exact payment

end YM.Integration.WilsonReportingCellRoute
