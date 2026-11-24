import YM.MS.Local.Labels

set_option autoImplicit false
noncomputable section
namespace YM.MS.Menus
open YM.MS.Local.Physical
variable {G:Gauge} (B: Deck G) {d:ℕ}
abbrev Glyph (B:Deck G)(d:ℕ):= Σ i:Fin (d+1),Σ j:Fin (i.val+1),B.BIndex i.val j.val
namespace Glyph
variable {B}
abbrev size (x:Glyph B d):= x.1.val
abbrev grade (x:Glyph B d):= x.2.1.val
abbrev read (x:Glyph B d):= B.raw x.size x.grade x.2.2
end Glyph
end YM.MS.Menus
