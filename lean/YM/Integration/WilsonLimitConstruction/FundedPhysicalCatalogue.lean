import YM.Integration.WilsonLimitConstruction.FundedRenderedBank

/-! Prices carried by the independently chosen cover model. Physical
finite-cutoff and winding identities use their own signed sources. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedPhysicalCatalogue
open Lattice Wilson RG Marker IterationFour IterationFour.Vacuum Comparison.RG02
open RG3.Script.Picnic LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open scoped Classical

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {B : Census V}
    {C : Family G} {J : Request V} {A : NumericSchedule C J} {d : LocalFormal.Datum C B}

structure Purchase (caps : Handoff.OutputCapacities) (K : NumericPrices A) (F : AnalyticInput J A d)
    extends FundedRenderedBank.Catalogue J d where
  rank_bounded : model.rankCap ≤ caps.packetRank
  power_bounded : model.powerCap ≤ caps.packetPower
  fine_layers : plan.layers (d.level+1)=F.layers
  output_layers_paid : Render.permits (plan.layers d.level) (A.outputNorm d.level)
  vacuum : GradedVacuumLayers (plan.layers d.level) (A.outputNorm d.level)
    J.order caps.vacuumRank (A.outputWidth d.level) (K.geometry d.level)
  region : Comparison.Density.Testing.Region (fun v => (J.tests v).Mood) (C.side d.level d.period)
  coverOffset : ℕ
  coverSlope : ℕ
  cover_cost : Real.exp ((A.outputNorm d.level).supportExponent*coverOffset) ≤ K.geometry d.level
  paid : model.Paid (A.outputNorm d.level) F.outputAddresses region
    (fun v => F.outputRadii v/F.kernelCosts v) (Pert.Asymptotics.regulatorRun C d.cutoff d.period (d.level+1))
    (A.outputWidth d.level) (K.geometry d.level) coverOffset coverSlope

variable {caps : Handoff.OutputCapacities} {K : NumericPrices A} {F : AnalyticInput J A d}

structure Width (width : ℕ→ℝ) (M : Purchase caps K F) where
  vacuum : GradedVacuumLayers (M.plan.layers d.level) (A.outputNorm d.level)
    J.order caps.vacuumRank (width d.level) (K.geometry d.level)
  paid : M.model.Paid (A.outputNorm d.level) F.outputAddresses M.region
    (fun v => F.outputRadii v/F.kernelCosts v) (Pert.Asymptotics.regulatorRun C d.cutoff d.period (d.level+1))
    (width d.level) (K.geometry d.level) M.coverOffset M.coverSlope

def own (M : Purchase caps K F) : Width A.outputWidth M := ⟨M.vacuum,M.paid⟩

def fine (M : Purchase caps K F) : FineWholeAction J d F.colors (M.plan.layers (d.level+1)) :=
  M.fine_layers.symm ▸ F.whole_input

end YM.Integration.WilsonLimitConstruction.FundedPhysicalCatalogue
end
