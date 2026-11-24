import YM.Integration.WilsonReceivedChronologicalRosterOccupiedTurn
import YM.Integration.WilsonOriginalCensusFundedUnits
import YM.Integration.WilsonOriginalCensusPhysicalUnits
import YM.Integration.WilsonReceivedChronologicalRosterMoment
import YM.Integration.WilsonReceivedCanonicalVerseBasis

/-! The elected signed portfolio opens to the original uncut product on the incoming K law. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalRosterRestriction
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

include valid κ pt in
theorem scalar (simple:G.Simple)(j:Fin n)(zero:grades j=0)(U:Config G (R.family.side K per)):
    WilsonPositionProgramBlockedTrialAddBack.uncut R (grades j) N per K (ξ j) (v j) U=v j 0:=by
  classical
  rw [WilsonReceivedCanonicalVerseBasis.letter R grades κ pt N per K valid v ξ j U]
  rw [Finset.sum_eq_single (.inl ())]
  · obtain ⟨reward,one⟩:=WilsonOriginalCensusSocketUnit.bare R grades N per K v j U (ξ j)
    rw [reward]
    have unit:=WilsonReceivedCanonicalVerseBasis.field R grades κ pt j (.inl ()) U (ξ j)
    have placed:=unit.trans one
    dsimp only [restored]
    simp only [placed, Complex.ofReal_one, mul_one]
    simp [WilsonThermometerDeclaredSeeds.entry, WilsonOriginalStarSceneWords.pole]
  · intro a _ off
    cases a with
    | inl z =>cases z;exact (off rfl).elim
    | inr sock =>rw [WilsonOriginalCensusSocketUnit.socket R simple grades N per K v j (by omega) sock,zero_mul]
  · simp

include valid κ pt in
theorem original (simple:G.Simple)(U:Config G (R.family.side K per)):
    product R grades (N:=N) v ξ s U=
      (∏j∈s.val.filter (fun j=>grades j=0),v j 0)*
       ∏j∈s.val.filter (fun j=>¬grades j=0),WilsonPositionProgramBlockedTrialAddBack.uncut R (grades j) N per K (ξ j) (v j) U:=by
  classical
  unfold product
  rw [Finset.prod_coe_sort s.val (fun j=>WilsonPositionProgramBlockedTrialAddBack.uncut R (grades j) N per K (ξ j) (v j) U),←Finset.prod_filter_mul_prod_filter_not s.val (fun j=>grades j=0) (fun j=>WilsonPositionProgramBlockedTrialAddBack.uncut R (grades j) N per K (ξ j) (v j) U)]
  congr 1
  exact Finset.prod_congr rfl fun j mem=>scalar R grades κ pt valid v ξ simple j (Finset.mem_filter.mp mem).2 U

end YM.Integration.WilsonReceivedChronologicalRosterRestriction
end
