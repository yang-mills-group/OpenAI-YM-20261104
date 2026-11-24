import YM.Integration.FullQLocalCanonicalForcedOutput

/-!
The transported-width conclusion of the full manuscript qlocal hypothesis.
The actual output model is selected once. It retains both its old numerical
width receipt and the width needed by the following input. This is a richer
hypothesis interface, not a proof of qlocal and not an upgrade of an existing
arbitrary CompleteGrant.

The manuscript's analytic packet convention pays output path length by the
input length divided by the block ratio, with one-stage lookahead. Merely
retuning coefficients preserves path lengths and does not prove this record.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.FullQLocal.RenderedStep.Numeric.Transported
open Filter Lattice Wilson RG Marker MeasureTheory
open RG3.Script.Picnic Comparison.RG02
open IterationFour IterationFour.Vacuum
open LocalComparison LocalComparison.Global
open scoped Topology BigOperators Classical

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V]
    {Gamma : Census V} {C : Family G}
    {J : Request V} {A : NumericSchedule C J}
    {caps : Handoff.OutputCapacities}

omit [DecidableEq V] [Fintype V] in
/-- The requested width at the next lower input. At level zero no further
step is asserted; truncating subtraction only makes this a total function. -/
def nextWidth (A : NumericSchedule C J) (m : ℕ) : ℝ :=
  A.inputWidth (m - 1)

/-- Additional exponential receipts on the identical full output model.
The old half-width receipts remain the original fields of M. -/
structure WidthReceipt {datum : LocalFormal.Datum C Gamma} {Y : Bulk.Chain C.path}
    {K : NumericPrices A} {F : AnalyticInput J A datum}
    (M : AnalyticOutput caps Y K F) where
  vacuum : GradedVacuumLayers (M.plan.layers datum.level) (A.outputNorm datum.level)
    J.order caps.vacuumRank (nextWidth A datum.level) (K.geometry datum.level)
  paid : M.model.Paid (A.outputNorm datum.level) F.outputAddresses M.region
    (fun v => F.outputRadii v / F.kernelCosts v)
    (Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (datum.level + 1))
    (nextWidth A datum.level) (K.geometry datum.level) M.coverOffset M.coverSlope

/-- Both width receipts precede every calibration family and rough input. -/
structure ModelFamily (caps : Handoff.OutputCapacities) (Y : Bulk.Chain C.path)
    (J : Request V) (A : NumericSchedule C J) (floor n : ℕ → ℕ) where
  original : Retained.ModelFamily (R := Gamma) caps Y J A floor n
  transported (datum : LocalFormal.Datum C Gamma) (hfirst : original.first ≤ datum.level)
      (hfloors : Handoff.LocalFloors floor n datum)
      (hulls : Retained.ShortHulls original.prices datum) (F : AnalyticInput J A datum) :
    WidthReceipt (original.realize datum hfirst hfloors hulls F)

/-- Full qlocal with its transported analytic packet convention retained.
Its prices are selected with both receipts, not identified with the prices
of an independently selected older grant. -/
structure Grant (caps : Handoff.OutputCapacities) (Y : Bulk.Chain C.path)
    (J : Request V) (A : NumericSchedule C J) (floor n : ℕ → ℕ)
    (pre : LocalComparison.Global.PreBlockConstant) where
  models : ModelFamily (Gamma := Gamma) caps Y J A floor n
  vacuum_constant : models.original.prices.vacuumConstant = pre.value
  polynomial_degree : models.original.prices.polynomialDegree = pre.degree
  physical (eta_w : ℕ → ℕ → ℕ → ℝ)
      (flat : Retained.UniformlyFlat (C := C) J eta_w) :
    Nonempty (Canonical.CompleteFamily models.original eta_w)

variable {Y : Bulk.Chain C.path} {floor n : ℕ → ℕ}
    {pre : LocalComparison.Global.PreBlockConstant}

/-- Project the same selected model family and physical continuation. -/
def Grant.forget (H : Grant (Gamma := Gamma) caps Y J A floor n pre) :
    Canonical.CompleteGrant (Gamma := Gamma) caps Y J A floor n pre where
  models := H.models.original
  vacuum_constant := H.vacuum_constant
  polynomial_degree := H.polynomial_degree
  physical := H.physical

/-- Choose only the complete physical family; the model and both widths
were already fixed before this calibration family was supplied. -/
def Grant.family (H : Grant (Gamma := Gamma) caps Y J A floor n pre)
    (eta_w : ℕ → ℕ → ℕ → ℝ) (flat : Retained.UniformlyFlat (C := C) J eta_w) :
    Canonical.CompleteFamily H.models.original eta_w :=
  Classical.choice (H.physical eta_w flat)

/-- This forgetful projection uses exactly the same choice expression. -/
theorem Grant.family_forget (H : Grant (Gamma := Gamma) caps Y J A floor n pre)
    (eta_w : ℕ → ℕ → ℕ → ℝ) (flat : Retained.UniformlyFlat (C := C) J eta_w) :
    H.forget.family eta_w flat = H.family eta_w flat := rfl

/-- The useful receipt is on the actual model of every selected output. -/
def Grant.selected_widths (H : Grant (Gamma := Gamma) caps Y J A floor n pre)
    (eta_w : ℕ → ℕ → ℕ → ℝ) (flat : Retained.UniformlyFlat (C := C) J eta_w)
    (datum : LocalFormal.Datum C Gamma)
    (hfirst : (H.family eta_w flat).joint.first ≤ datum.level)
    (hfloors : Handoff.LocalFloors floor n datum)
    (hulls : Retained.ShortHulls H.models.original.prices datum)
    (F : AnalyticInput J A datum) :
    WidthReceipt (H.models.original.realize datum
      ((H.family eta_w flat).joint.after_model.trans hfirst) hfloors hulls F) :=
  H.models.transported datum
    ((H.family eta_w flat).joint.after_model.trans hfirst) hfloors hulls F

/-- In particular, the old width and the useful width refer to one list,
one model, one price, and one actual input; there is no second realization. -/
theorem Grant.selected_vacuum_widths
    (H : Grant (Gamma := Gamma) caps Y J A floor n pre)
    (eta_w : ℕ → ℕ → ℕ → ℝ) (flat : Retained.UniformlyFlat (C := C) J eta_w)
    (datum : LocalFormal.Datum C Gamma)
    (hfirst : (H.family eta_w flat).joint.first ≤ datum.level)
    (hfloors : Handoff.LocalFloors floor n datum)
    (hulls : Retained.ShortHulls H.models.original.prices datum)
    (F : AnalyticInput J A datum) :
    let M := H.models.original.realize datum
      ((H.family eta_w flat).joint.after_model.trans hfirst) hfloors hulls F
    Nonempty (GradedVacuumLayers (M.plan.layers datum.level) (A.outputNorm datum.level)
      J.order caps.vacuumRank (A.outputWidth datum.level)
      (H.models.original.prices.geometry datum.level)) ∧
    Nonempty (GradedVacuumLayers (M.plan.layers datum.level) (A.outputNorm datum.level)
      J.order caps.vacuumRank (nextWidth A datum.level)
      (H.models.original.prices.geometry datum.level)) := by
  dsimp only
  exact ⟨⟨(H.models.original.realize datum
    ((H.family eta_w flat).joint.after_model.trans hfirst) hfloors hulls F).vacuum⟩,
    ⟨(H.selected_widths eta_w flat datum hfirst hfloors hulls F).vacuum⟩⟩

end YM.Integration.FullQLocal.RenderedStep.Numeric.Transported
end
