import YM.FormalOPE.RG10.CommonStamps
import YM.UVExtension.Oasis.Flora
import YM.Next.FOUNDATIONS.Primary

/-! Adapter selecting the actual common unmasked top stencils (final was chosen once outside).
This is not selecting an OPE prescription, and it isn't transporting any physical witness or
asserting positive-order estimates. Just the *stencil data*, with the named valuation hypotheses
for the elaborated UV provider. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10

open UVExtension Lattice

/-- Supply the valuation premises of `InversionTop.Stamp.native` for the common stencils. -/
theorem supplies {G : Gauge} {hG : G.Simple} {C : Family G} (h : Oasis.Floral (hG:=hG) C) :
    ∀ d, Bid.pop (C.localSection d) := by
  obtain ⟨M,B,A,R,S,T,t,K,w,Q,L,H,rfl,hS,hc,hB,hQ,hR,h'⟩:= h
  exact fun d => Next.Foundations.valuation G d
end YM.FormalOPE.RG10
