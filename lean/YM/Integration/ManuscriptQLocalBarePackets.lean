import YM.Integration.ManuscriptQLocalActualLog

/-! The primitive coefficient price of the submitted marked packet before multiplication by its physical coupling. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ManuscriptQLocalOriginalSourceGrade
open Lattice Wilson RG Marker PhysicalNext.Repeat.Legato LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open IterationFour IterationFour.Vacuum RG3.Script.Picnic
open scoped Classical
variable {G:Gauge} {V:Type} [DecidableEq V] [Fintype V] {Γ:Census V} {C:Family G}
  {J:Request V} {A:NumericSchedule C J} {d:LocalFormal.Datum C Γ} (F:AnalyticInput J A d)

abbrev Bare := F.packets.Paid (A.inputNorm d.level) F.inputAddresses F.inputRegion (fun v=>F.inputRadii v/F.kernelCosts v) 1
  (A.inputWidth d.level) (A.admittedCost d.level) F.coverOffset F.coverSlope

lemma zero_power (power:∀i,F.packets.power i=0) : Bare F := by
  let H:=F.input_paid
  refine {
    width_pos := H.width_pos
    positive := H.positive
    coefficient := H.coefficient
    paths := H.paths
    addresses := H.addresses
    symmetry := H.symmetry
    reads := H.reads
    multilinear := H.multilinear
    cover := H.cover
    width_reserved := H.width_reserved
    roots := ?_ }
  intro v;simpa only [power,zpow_zero] using H.roots v

end YM.Integration.ManuscriptQLocalOriginalSourceGrade
end
