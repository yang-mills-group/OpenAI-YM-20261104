import YM.Integration.FullQLocalTransportedWidth

/-!
The prescribed output-width part of the full qlocal hypothesis.
One canonical model family carries the added receipt before calibration and
rough input. The old transported width is recovered only when it is exactly
the prescribed width; an arbitrary wider receipt is not inferred.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.FullQLocal.RenderedStep.Numeric.Prescribed
open Filter Lattice Wilson RG Marker MeasureTheory
open RG3.Script.Picnic Comparison.RG02
open IterationFour IterationFour.Vacuum
open LocalComparison LocalComparison.Global
open scoped Topology BigOperators Classical

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V]
    {Gamma : Census V} {C : Family G}
    {J : Request V} {A : NumericSchedule C J}
    {caps : Handoff.OutputCapacities}

/-- Exact additional exponential receipts for the original output model. -/
structure WidthReceipt {datum : LocalFormal.Datum C Gamma} {Y : Bulk.Chain C.path}
    {K : NumericPrices A} {F : AnalyticInput J A datum}
    (width : ℕ → ℝ) (M : AnalyticOutput caps Y K F) where
  vacuum : GradedVacuumLayers (M.plan.layers datum.level) (A.outputNorm datum.level)
    J.order caps.vacuumRank (width datum.level) (K.geometry datum.level)
  paid : M.model.Paid (A.outputNorm datum.level) F.outputAddresses M.region
    (fun v => F.outputRadii v / F.kernelCosts v)
    (Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (datum.level + 1))
    (width datum.level) (K.geometry datum.level) M.coverOffset M.coverSlope

/-- The prescribed receipt is attached to the same canonical family.
The structure is an assumed full-q conclusion, not a theorem proving qlocal. -/
structure Grant (caps : Handoff.OutputCapacities) (Y : Bulk.Chain C.path)
    (J : Request V) (A : NumericSchedule C J) (floor n : ℕ → ℕ)
    (pre : LocalComparison.Global.PreBlockConstant) (width : ℕ → ℝ) where
  original : Canonical.CompleteGrant (Gamma := Gamma) caps Y J A floor n pre
  prescribed (datum : LocalFormal.Datum C Gamma)
      (hfirst : original.models.first ≤ datum.level)
      (hfloors : Handoff.LocalFloors floor n datum)
      (hulls : Retained.ShortHulls original.models.prices datum)
      (F : AnalyticInput J A datum) :
    WidthReceipt width (original.models.realize datum hfirst hfloors hulls F)

variable {Y : Bulk.Chain C.path} {floor n : ℕ → ℕ}
    {pre : LocalComparison.Global.PreBlockConstant} {width : ℕ → ℝ}

/-- Forget only the added prescribed-width proof, retaining all actual data. -/
def Grant.forget (H : Grant (Gamma := Gamma) caps Y J A floor n pre width) :
    Canonical.CompleteGrant (Gamma := Gamma) caps Y J A floor n pre :=
  H.original

/-- The one canonical choice on the already fixed model family. -/
def Grant.family (H : Grant (Gamma := Gamma) caps Y J A floor n pre width)
    (eta_w : ℕ → ℕ → ℕ → ℝ) (flat : Retained.UniformlyFlat (C := C) J eta_w) :
    Canonical.CompleteFamily H.original.models eta_w :=
  H.original.family eta_w flat

theorem Grant.family_forget
    (H : Grant (Gamma := Gamma) caps Y J A floor n pre width)
    (eta_w : ℕ → ℕ → ℕ → ℝ) (flat : Retained.UniformlyFlat (C := C) J eta_w) :
    H.forget.family eta_w flat = H.family eta_w flat := rfl

/-- The prescribed width belongs to the model of this actual selected output. -/
def Grant.selected_widths (H : Grant (Gamma := Gamma) caps Y J A floor n pre width)
    (eta_w : ℕ → ℕ → ℕ → ℝ) (flat : Retained.UniformlyFlat (C := C) J eta_w)
    (datum : LocalFormal.Datum C Gamma)
    (hfirst : (H.family eta_w flat).joint.first ≤ datum.level)
    (hfloors : Handoff.LocalFloors floor n datum)
    (hulls : Retained.ShortHulls H.original.models.prices datum)
    (F : AnalyticInput J A datum) :
    WidthReceipt width (H.original.models.realize datum
      ((H.family eta_w flat).joint.after_model.trans hfirst) hfloors hulls F) :=
  H.prescribed datum ((H.family eta_w flat).joint.after_model.trans hfirst)
    hfloors hulls F

/-- A literal width equality recovers the older transported interface. -/
def Grant.transported (H : Grant (Gamma := Gamma) caps Y J A floor n pre width)
    (hwidth : ∀ m, width m = Transported.nextWidth A m) :
    Transported.Grant (Gamma := Gamma) caps Y J A floor n pre where
  models := {
    original := H.original.models
    transported := fun datum hfirst hfloors hulls F => {
      vacuum := by
        simpa only [hwidth datum.level] using
          (H.prescribed datum hfirst hfloors hulls F).vacuum
      paid := by
        simpa only [hwidth datum.level] using
          (H.prescribed datum hfirst hfloors hulls F).paid } }
  vacuum_constant := H.original.vacuum_constant
  polynomial_degree := H.original.polynomial_degree
  physical := H.original.physical

/-- This comparison is between projections of one witness, not independent choices. -/
theorem Grant.transported_family
    (H : Grant (Gamma := Gamma) caps Y J A floor n pre width)
    (hwidth : ∀ m, width m = Transported.nextWidth A m)
    (eta_w : ℕ → ℕ → ℕ → ℝ) (flat : Retained.UniformlyFlat (C := C) J eta_w) :
    (H.transported hwidth).family eta_w flat = H.family eta_w flat := rfl

end YM.Integration.FullQLocal.RenderedStep.Numeric.Prescribed
end
