import YM.Integration.WilsonReceivedChronologicalRosterMoment
import YM.Integration.WilsonReceivedCanonicalVerseBasis

/-! The elected signed portfolio opens to the original uncut product on the incoming K law. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalRosterOccupiedTurn
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

def product (U:Config G (R.family.side K per)):ℂ:=
  ∏ j:s.val,WilsonPositionProgramBlockedTrialAddBack.uncut R (grades j) N per K (ξ j) (v j) U

include valid in
theorem original (rows:Selection R grades s.val → Config G (R.family.side K per) → Marker.Poly (Stock.census (Fin n)))
    (top:∀q U,(rows q U).part s=((R.family.path.rep N per K).eval U:ℂ)*
      word R grades κ pt (regulatorRun R.family N per K) ξ s.val q U):
    let numerator:=WilsonOriginalTwoFlatIRPoolSubfaceMaterial.numerator R grades (K:=K) (N:=N) v s rows
    let inlet:=product R grades (N:=N) v ξ s
    (∀U,numerator U=((R.family.path.rep N per K).eval U:ℂ)*inlet U) ∧
    ∀(e:ℕ)(older:e≤K),reading R (N:=N) numerator e older =
      actualTransport R.family (N:=N) inlet older 1 :=by
  classical
  intro numerator inlet
  have opened(U:Config G (R.family.side K per)):numerator U=((R.family.path.rep N per K).eval U:ℂ)*inlet U:=by
    change (∑q:Selection R grades s.val,weight R grades N per K v s.val q*(rows q U).part s)=_
    have assembly:=WilsonReceivedCanonicalVerseBasis.faces R grades κ pt N per K valid v ξ s.val U
    change inlet U = ∑q:Selection R grades s.val, weight R grades N per K v s.val q *
      word R grades κ pt (regulatorRun R.family N per K) ξ s.val q U at assembly
    rw [assembly,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    rw [top q U]
    ring
  refine ⟨opened,?_⟩
  intro e older
  have density:numerator=WilsonThermometerUnitFilingFlatTelescope.numerator R N per K inlet:=funext opened
  rw [density]
  exact WilsonThermometerUnitFilingPosterior.weighted R _ _

end YM.Integration.WilsonReceivedChronologicalRosterOccupiedTurn
end
