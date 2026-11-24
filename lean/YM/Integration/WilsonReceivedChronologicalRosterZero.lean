import YM.Integration.WilsonReceivedChronologicalRosterRestriction
import YM.Integration.WilsonAddressedCommonTrialWeights

/-! Exact removal of actual zero-grade columns from every earlier Wilson conditional. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalRosterZero
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


open WilsonThermometerUnitFilingCoarse (reading)
open WilsonReceivedCanonicalVersePortfolio (Selection weight)
open WilsonReceivedCanonicalVersePosterior (word)
open PhysicalNext.Repeat.Legato

variable {G:Gauge}(R:Run G){n N per K:ℕ}(grades:Fin n→ℕ){dims:Fin n→ℕ}
  (κ:(j:Fin n)→Knob (dims j))(pt:Fin n→Chamber)(valid:K≤N)
  (v:(i:Fin n)→R.family.label (grades i))(ξ:Fin n→Site (R.family.side K per))
  (s:(Stock.census (Fin n)).Mode)

open WilsonReceivedCanonicalVerseBasis (dose restored)
open WilsonThermometerDeclaredSeeds (Choice entry)
open WilsonOriginalStarSceneWords (pole)
open WilsonReceivedChronologicalRosterOccupiedTurn (product)

include κ pt valid in
theorem original (simple:G.Simple){l:ℕ}(lk:l ≤ K)(V:Config G (R.family.side l per)):
    actualTransport R.family (N:=N) (product R grades (N:=N) v ξ s) lk V=
      (∏j∈s.val.filter (fun j=>grades j=0),v j 0)*actualTransport R.family (N:=N)
        (fun U=>∏j∈s.val.filter (fun j=>¬grades j=0),
          WilsonPositionProgramBlockedTrialAddBack.uncut R (grades j) N per K (ξ j) (v j) U) lk V:=by
  classical
  rw [funext (WilsonReceivedChronologicalRosterRestriction.original R grades κ pt valid v ξ s simple)]
  exact WilsonAddressedCommonTrialWeights.scalar R valid lk _ _ V

include κ pt valid in
theorem units (simple:G.Simple){l:ℕ}(lk:l ≤ K)(V:Config G (R.family.side l per))
    (zero:∀j∈s.val,grades j=0):
    actualTransport R.family (N:=N) (product R grades (N:=N) v ξ s) lk V=∏j∈s.val,v j 0:=by
  classical
  rw [original R grades κ pt valid v ξ s simple lk V]
  have kept:s.val.filter (fun j=>¬grades j=0)=∅:=by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro j member
    rcases Finset.mem_filter.mp member with ⟨js,pos⟩
    exact pos (zero j js)
  have dropped:s.val.filter (fun j=>grades j=0)=s.val:=Finset.filter_eq_self.mpr zero
  simp only [kept,dropped,Finset.prod_empty]
  rw [actualTransport_const R.family R.makes valid (1:ℂ) lk V,mul_one]

end YM.Integration.WilsonReceivedChronologicalRosterZero
end
