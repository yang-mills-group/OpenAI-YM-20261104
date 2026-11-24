import YM.Integration.FullQLocalNumericStepData

/-! A positive ultraviolet vacuum Plan reads only the literal fine
list of physical Pieces and its legally issued range of grades. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedSpringFineInlet
open Lattice Wilson RG Marker IterationFour IterationFour.Vacuum LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {Γ : Census V} {Y : Family G}

structure Inlet (J : Request V) (_A : NumericSchedule Y J) (d : LocalFormal.Datum Y Γ) where
  layers : List (Piece G (Y.side (d.level+1) d.period))
  orders : Render.gradings layers J.order

variable {J : Request V} {A : NumericSchedule Y J} {d : LocalFormal.Datum Y Γ}

def original (F : AnalyticInput J A d) : Inlet J A d := ⟨F.layers,F.vacuum.orders⟩

instance : Coe (AnalyticInput J A d) (Inlet J A d) := ⟨original⟩

@[simp] theorem layers (F : AnalyticInput J A d) : (original F).layers=F.layers := rfl

end YM.Integration.WilsonLimitConstruction.FundedSpringFineInlet
