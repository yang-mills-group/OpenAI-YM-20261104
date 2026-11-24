import YM.FVA2.Scale.Functions
import YM.PhysMS.Frame.Measured
import YM.RG12.Canonical.Low

/-! Determine the actual rich indices of a simple gauge theory below dimension four.  There
are no unobserved positive-grade indices in a complete commissioned basis. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSubcriticalRichGlyph
open Function Filter Set Finset MS MS.Local.Physical MS.Menus MS.Land MS.Theater FVA2
open Extraction Climb Maxwell
open scoped Classical BigOperators
variable {G:Gauge} (C:Family G) (B:Deck G)

include C in
theorem card (hG:G.Simple) {h:ℕ} (low:h<4) : Fintype.card (Glyph B h)=1 :=
 (Module.finrank_eq_card_basis ((Daylight B h).map (Maxwell.Free.fields C.labels h).symm)).symm.trans
   (UVNext.FreeStress.dim_before C.labels hG low)

def lifted (h:ℕ) (b:B.BIndex 0 0) : Glyph B h := ⟨⟨0,Nat.zero_lt_succ _⟩,⟨⟨0,Nat.zero_lt_succ _⟩,b⟩⟩

include C in
theorem registered (hG:G.Simple) : ∃ b:B.BIndex 0 0,∀h:ℕ,h<4→∀ a:Glyph B h, a=lifted B h b := by
 have pos:0<Fintype.card (Glyph B 0):=by rw [card C B hG (h:=0) (by decide)];decide
 obtain ⟨⟨⟨i,hi⟩,⟨⟨j,hj⟩,v⟩⟩⟩:=Fintype.card_pos_iff.mp pos
 have ei:i=0:=by omega
 subst i
 have ej:j=0:=by omega
 subst j
 refine ⟨v,fun h hh a=>Fintype.card_le_one_iff.mp (le_of_eq (card C B hG hh)) a (lifted B h v)⟩

end YM.Integration.WilsonSubcriticalRichGlyph
