import YM.Integration.FullQLocalPrescribedWidth

/-! A larger finite floor only restricts the domain of a prescribed grant. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.PrescribedGrantFloors

open Lattice RG Marker Comparison.RG02
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V]
  {C : Family G} {Γ : Census V} {J : Request V} {A : NumericSchedule C J}
  {Y : Bulk.Chain C.path} {caps : Handoff.OutputCapacities}
  {lo hi n : ℕ → ℕ} (h : lo ≤ hi)
  {pre : LocalComparison.Global.PreBlockConstant} {width : ℕ → ℝ}

omit [Fintype V] in
theorem lower (h : lo ≤ hi) {d : LocalFormal.Datum C Γ} (p : Handoff.LocalFloors hi n d) :
    Handoff.LocalFloors lo n d := ⟨(h _).trans p.1, (h _).trans p.2⟩

def models (M : Retained.ModelFamily (R := Γ) caps Y J A lo n) :
    Retained.ModelFamily (R := Γ) caps Y J A hi n where
  prices := M.prices
  first := M.first
  realize d hd hf hull F := M.realize d hd (lower h hf) hull F

variable {M : Retained.ModelFamily (R := Γ) caps Y J A lo n}
  {eta : ℕ → ℕ → ℕ → ℝ}

def joint (B : Retained.JointFamily M eta) :
    Retained.JointFamily (models h M) eta where
  first := B.first
  after_model := B.after_model
  select d hd hf hull F I intake := B.select d hd (lower h hf) hull F I intake
  bounds delta hdelta order := by
    obtain ⟨k, hk, hb⟩ := B.bounds delta hdelta order
    exact ⟨k, hk, fun d hd hf hull F I intake =>
      hb d hd (lower h hf) hull F I intake⟩

def family (B : Canonical.CompleteFamily M eta) :
    Canonical.CompleteFamily (models h M) eta where
  joint := joint h B.joint
  reserve d hd hf hull F I intake := B.reserve d hd (lower h hf) hull F I intake
  canonical d hd hf hull F I intake := B.canonical d hd (lower h hf) hull F I intake
  canonical_bounds delta hdelta order := by
    obtain ⟨k, hk, hb⟩ := B.canonical_bounds delta hdelta order
    exact ⟨k, hk, fun d hd hf hull F I intake =>
      hb d hd (lower h hf) hull F I intake⟩

/-- This restricts the domain of the same analytic model, canonical output,
forced reserve and rough-input bounds to the stronger pair of local floors. -/
def grant (H : Prescribed.Grant (Gamma := Γ) caps Y J A lo n pre width) :
    Prescribed.Grant (Gamma := Γ) caps Y J A hi n pre width where
  original := {
    models := models h H.original.models
    vacuum_constant := H.original.vacuum_constant
    polynomial_degree := H.original.polynomial_degree
    physical := fun eta flat => (H.original.physical eta flat).map (family h) }
  prescribed d hd hf hull F := H.prescribed d hd (lower h hf) hull F

theorem prices (H : Prescribed.Grant (Gamma := Γ) caps Y J A lo n pre width) :
    (grant h H).original.models.prices = H.original.models.prices := rfl

end YM.Integration.WilsonLimitConstruction.PrescribedGrantFloors
end
