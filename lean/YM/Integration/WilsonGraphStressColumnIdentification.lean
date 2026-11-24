import YM.Integration.WilsonGraphSignedStressSpan

/-! Express the grade-four signed tensor on the unit, the diagonal panel, the sum
of unordered squares, and the translation-normalized Maxwell stress. -/
set_option autoImplicit false
noncomputable section

namespace YM.UVNext.FreeStress.Uncentered
open Maxwell Labels Climb Table Work.A01 Next.UVStress
variable {G : Gauge} (F : Frames G)

/-- `total` counts each unordered plane twice. Its quarter supplies the trace
term of the translation-normalized Maxwell stress. -/
theorem normalizedColumns (d a b c : ℂ) (i j : Axis) :
    fields F d a b c i j =
      d • (if i = j then (freeTable F).unit 4 else 0) +
      (a - 2*b - c) • (if i = j then near F i else 0) +
      (2*b + c/2) • (if i = j then (1/2 : ℂ) • total F else 0) +
      (-c) • (-panel F i j + (if i = j then (1/4 : ℂ) • total F else 0)) := by
  by_cases hij : i = j
  · subst j
    have decompose (u x y : FourFields F) :
        d • u + a • x + b • y =
          d • u + (a - 2*b - c) • x +
            (2*b + c/2) • ((1/2 : ℂ) • ((2 : ℂ) • x + y)) +
            (-c) • (-x + (1/4 : ℂ) • ((2 : ℂ) • x + y)) := by
      module
    simpa [fields, east, west, across, splitDiag, total_at F i, near] using
      decompose ((freeTable F).unit 4) (near F i) (far F i)
  · simp [fields, east, west, across, splitDiag, hij]

end YM.UVNext.FreeStress.Uncentered

