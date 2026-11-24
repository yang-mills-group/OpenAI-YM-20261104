import YM.Integration.WilsonIndependentCollarDatedAddressed
import YM.Integration.WilsonReceivedCanonicalVerseBasis

/-! At the first upper date the genuine canonical socket itself supplies
the incoming group word. The first lower chronological pupil starts with
these same stencil labels, including their numerical finite-cutoff doses. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentCollarDatedUpperBasis
open Finset Function Lattice RG Wilson Precision PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer WilsonCoeffUV.Soil
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Embroider
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Blue WilsonCoeffUV.Winding WilsonCoeffUV.Wheel.Express
open WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Wheel.Cadenza QuadraticLocal Multi Marker
open WilsonReceivedFixedDigitHistory WilsonReceivedCanonicalVerseBasis WilsonThermometerDeclaredSeeds
open FundedMarkedPathSelection
open WilsonReceivedCanonicalVerseRegister (start)
open WilsonReceivedFixedDigitCanonical (fixed)
open Pert.Asymptotics
open scoped Classical BigOperators
variable {G:Gauge}{n:ℕ}(R:Run G)(k D:Fin n→ℕ)(κ:(v:Fin n)→Knob (D v))(pt:Fin n→Chamber)

theorem original (N per K:ℕ)(cut:K≤N)(cells:Digits R.family.path.levels (Fin n))
    (doses:(v:Fin n)→R.family.label (k v))(port:Fin n→Site (R.family.side K per)):
    (∀seed:(v:Fin n)→Choice R k v, fixed R k κ pt N K K cells seed=start R k κ pt seed) ∧
    ∀(S:Finset (Fin n))(U:Config G (R.family.side K per)),
      (∏j:S,WilsonPositionProgramBlockedTrialAddBack.uncut R (k j) N per K (port j) (doses j) U)=
        ∑seed:(j:S)→Choice R k j,(∏j:S,dose R k N per K doses j (seed j))*
          ∏j:S,restored R k κ pt (regulatorRun R.family N per K) j (seed j) (port j) U:=by
  refine ⟨fun seed=>?_,WilsonReceivedCanonicalVerseBasis.faces R k κ pt N per K cut doses port⟩
  simp only [fixed,Nat.sub_self,itinerary]

end YM.Integration.WilsonIndependentCollarDatedUpperBasis
end
