import YM.FVA2.Notch.Sales
import YM.TraceExtension.Checks.Colors
/-!
 # Concrete instance (defining-representation SU(2))

 To verify non-vacuity. Uses inspected baseline example `Trace.Col.duo`.
 `stair`: ratio exactly three (powers-of-three family).
 Can also take another `Run` with this example.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Notch
open XSpace Lattice Next.Foundations
open Register Register.WilsonPrescription
private abbrev G:= SUtwo

def stair:Run:= ⟨3,by decide,1,⟨4,by decide,by decide⟩,by decide,by decide⟩
/-- For the displayed SUtwo gauge and schedule, the formal OPE supplier
works at every scale without a further γ-consistency estimate. -/
lemma Nontriv : ∃ (N:Register.WilsonPrescription SUtwo)(T:MS.Land.MS_Data SUtwo (Position.OpenAxis.Plot (Press.portDeck SUtwo)))(M: MS.Land.Prescription ( Press.portDeck SUtwo)), N.run=stair∧ M.team=( Continuum.Continuation.proofStart Trace.Col.duo (Reg.supplies N.scheme T) false ).team ∧ Teller.Homes.Installed N.scheme T M true ∧ Served N T M ∧ Poise N T M ∧ ∀ ν:ℝ,O.Canon.Supplied N T ν:= by
    obtain ⟨N,T,M,hN,hM,H,x,v⟩:= Inked.enroll G Trace.Col.duo stair false; exact ⟨N,T,M,hN,hM,H,x,coverage N T M Trace.Col.duo x,v⟩
end YM.FVA2.Notch
