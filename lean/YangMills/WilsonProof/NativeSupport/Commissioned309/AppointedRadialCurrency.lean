import YM.GradedFar.G
import YM.GradedFar.Continuation.Windows

namespace YM.FVA2.GradedFar.AppointedRadialCurrency
open Continuation

theorem radius (G : Gauge) (r : ℝ) : meter G r = gYM G r := rfl

theorem price (G : Gauge) (r : ℝ) (p : ℕ) :
    (meter G r) ^ (p + 1) = (gYM G r) ^ (p + 1) := rfl

theorem window (G : Gauge) (C B : ℝ) (w : Window) :
    w.Stretch ≤ C * (meter G w.len) ^ (-B) ↔ w ∈ upper G C B := Iff.rfl

theorem allWindows (G : Gauge) (C B : ℝ) :
    Window.windows {w : Window | w.Stretch ≤ C * (meter G w.len) ^ (-B)} =
      Window.windows (upper G C B) := rfl

end YM.FVA2.GradedFar.AppointedRadialCurrency

