import YM.UVExtension.Oasis.Flora
import YM.Next.FOUNDATIONS.Primary
import YM.RG06.Section.Lens

/-!
# The common C actually supplies the `Bid.pop` adapter

No appeal to `PertExtension.FirstBridge.stamped_actual_exists` etc.
The common provider in the pinned contract already exports Floral on C.
-/
set_option autoImplicit false
namespace YM.RG06.Section
open scoped BigOperators
open Lattice Source Labels RG Extraction
variable {G : Gauge} {hG : G.Simple}{C:Family G}

theorem origin (h: UVExtension.Oasis.Floral (hG:=hG) C)(d:ℕ): Bid.pop (C.localSection d):=by
  obtain ⟨M,P,A,R,S,T,t,K,w,Q,L,_arc,hC,_⟩:=h
  rw [hC]
  exact Next.Foundations.valuation G d

theorem floral_ledger (H: C.Makes)(h : UVExtension.Oasis.Floral (hG:=hG) C)(d:ℕ):
    ∃ (I : Finset (Push.CutoffProjectors.Lens G d))(c:ℝ), 0<c ∧ ∀ v:C.label d,c*‖v‖≤ ∑ i∈ I,‖profiles (C.localSection d) v i‖ :=
  ledger _ (H.sections d) (origin h d)
end YM.RG06.Section
