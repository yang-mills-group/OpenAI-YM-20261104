import YM.FVA2.PoleUnit

/-! The actual commissioned MS polynomial below dimension four is a coupling-independent
constant, with its true bare normalization and no nonempty field words. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSubcriticalRichOptics
open MS MS.Plane MS.Arts MS.Koszul MS.Mach MS.Motif MS.Motif.Literal MS.Land MS.Rake MS.Local.Physical MS.Menus
open FVA2 FVA2.ColorCode
open scoped Classical BigOperators
variable {G:Gauge} {B:Deck G} (A:Booked B)

abbrev valueAtUnit (j:Plaid B 0):ℂ:=(Land.read j).read []

theorem issued (j:Plaid B 0):A.optics 0 j=Finsupp.single 0 (Frost.pile (valueAtUnit j)):=by
  apply Frost.king _ (L:=(Land.read j).read)
  have low:(Land.read j).grade=0:=Nat.eq_zero_of_le_zero (Glyph.memory (Land.read j))
  convert A.law 0 j using 2
  exact low.symm

end YM.Integration.WilsonSubcriticalRichOptics
