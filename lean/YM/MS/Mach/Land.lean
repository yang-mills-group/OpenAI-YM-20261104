import YM.MS.Mach.Pick
import YM.MS.Menus.Glyph

set_option autoImplicit false
noncomputable section
namespace YM.MS.Land
open Local.Physical Menus Motif.Literal Arts Mach

variable {G:Gauge} {d:ℕ} {B:Deck G}
abbrev Plaid (B:Deck G)(d:ℕ) := Σ i: Fin (d+1), B.BIndex d i.val
def read (i:Plaid B d): Glyph B d:= ⟨ ⟨d,Nat.lt_succ_self d⟩,i ⟩
structure Booked (B:Deck G) where
   optics (d:ℕ) (i: Plaid B d): Box (Mob G)
   law d i: Ele d (read i).grade (read (B:=B) i).read (optics d i)
end YM.MS.Land
