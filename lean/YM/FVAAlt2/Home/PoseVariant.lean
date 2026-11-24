import YM.FVAAlt2.Home.Waltz
import YM.Pert.Lattice.Lifts
/-! Select ONCE the classical lift on symmetric polynomials.
 It is allowed both as an RG10.Position (H-equiv+grade across heights), AND for the
 auxiliary-regulator native $LPT of just Triangle detector computation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.Home
open Function Lattice Filter Labels Source Maxwell Pert.RawLabels
open Extraction Extra.FD PertExtension FormalOPE FormalOPE.RG10
open FormalOPE.RG10.Position (Loft)
variable {G:Gauge}(F:Frames G) {d m k:ℕ}
def LoftPP (F:Frames G) : Loft F:= ⟨physicalLabel F⟩
lemma warmPP (x: (freeTable F).Field d) : observable G d (physicalLabel F d x)= writes F d x := by rw [ ← RG10.Position.form F d (physicalLabel F d x) ]; exact congr_arg _ ( physical_round F x )
lemma localPP (x:(freeTable F).Field d): physicalLabel F d x=fixedPolynomial G d ((Loft.preliminary F).lift d x) := by
 let u:= ( Loft.preliminary F).lift d x; rw [ ← embed_round F ]; refine congr_arg _ ( writes_inj F d ?_ ); exact ( Loft.warmth d (x:=x) ).symm.trans ( Position.form F d u ).symm
lemma readyPP : Loft.Level F (LoftPP F):= by
   constructor; · exact fun _=> warmPP F
   · intro d m x hp; change physicalLabel F d x∈ _; rw [localPP F]; obtain hv:= Loft.homogeneity d m hp; let u:Label G d:= (Loft.preliminary F).lift d x; change fixedPolynomial G d u ∈ _; rw [← show gradePart m u=u from gradePart_self u m hv,← fixed_pure ]; exact gradePart_mem ..
   · intro d j x; exact (physical_ortho F j.ortho x).symm
   · intro d x; exact (physical_real F x (table_spin F)).symm
   · intro d; exact physical_unit F d
   intro d e h x; change physicalLabel F e ( Position.higher F h x )=raiseLabel G h (physicalLabel F d x); rw [localPP, localPP F x,Loft.upper h,fixed_includes]
end YM.FVAAlt2.Home
