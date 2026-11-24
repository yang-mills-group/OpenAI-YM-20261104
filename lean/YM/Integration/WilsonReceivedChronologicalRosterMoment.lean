import YM.Integration.WilsonOriginalTwoFlatIRPoolSubfaceMaterial

/-! Complete ordinary printed fields and conditional reads on their own original finite wallet. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalRosterMoment
open Finset Function Lattice Wilson RG Marker Source Labels Trace.Pilot OPE
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonOriginalMixedBlockRows
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Extra.Histories Extra.Trajectories Extra.Multi
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Embroider
open WilsonMovingForkPrintedFile (parent Board)
open WilsonMovingForkStencilCatalogue (Catalogue table)
open WilsonMovingForkDepositedPrint (Sheet board polynomial)
open WilsonMovingForkStencilLine (Received)
open WilsonReceivedCanonicalVersePortfolio (Selection weight)
open WilsonOriginalTwoFlatIRPoolSubfaceCourse (expanded)
open WilsonThermometerUnitFilingCoarse (reading)
open Pert.Asymptotics Planned.GuardedAtom Extra.Histories Next.Foundations
open RG16 RG16.Literal Trace.Physical.GermGraph
open RG12 Bid Extra.Histories.Relay MergeProof MergeProof.Accent Overlay Cells Trace.Physical
open scoped Classical BigOperators


variable {G:Gauge}(R:Run G){n K N per i:ℕ}(grades:Fin n→ℕ)
  (source:Catalogue R grades K)(v:∀j,R.family.label (grades j))
  (ξ:Fin n→Site (R.family.side K per))(live:i<K)(s:(Stock.census (Fin n)).Mode)
  (raw:Selection R grades s.val → Config G (R.family.side i per) → Marker.Poly (Stock.census (Fin n)))

def Heard : Prop :=
  let numerator:=WilsonOriginalTwoFlatIRPoolSubfaceMaterial.numerator R grades (K:=K) (N:=N) v s raw
  let field:=WilsonOriginalTwoFlatIRPoolSubfaceMaterial.word R grades (N:=N) source v ξ live s
  (∀q,∃H:Sheet R N i (parent R live.le per ξ),
      source N per ξ (expanded R grades s q) i live=some H ∧ Received H (raw q)) ∧
  (∀U,numerator U=((R.family.path.rep N per i).eval U:ℂ)*field U) ∧
  (∀ (e : ℕ) (he : e ≤ i), reading R (N:=N) numerator e he =
    reading R (N:=N) (fun U=>((R.family.path.rep N per i).eval U:ℂ)*field U) e he) ∧
  reading R (N:=N) numerator i le_rfl=field 1

theorem original (received:∀q,∃H:Sheet R N i (parent R live.le per ξ),
    source N per ξ (expanded R grades s q) i live=some H ∧ Received H (raw q)) :
    Heard R grades (N:=N) source v ξ live s raw := by
  have whole:=WilsonOriginalTwoFlatIRPoolSubfaceMaterial.original R grades source v ξ live s raw received
  exact ⟨received,fun U=>(whole.1 U).symm,
    WilsonOriginalTwoFlatIRPoolSubfaceMaterial.stops R grades source v ξ live s raw received⟩

end YM.Integration.WilsonReceivedChronologicalRosterMoment
end
