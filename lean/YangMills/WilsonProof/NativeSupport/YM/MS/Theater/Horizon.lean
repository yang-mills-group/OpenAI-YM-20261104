import YM.MS.Theater.Horizon
import YangMills.WilsonProof.NativeSupport.YM.MS.Theater.DataK
import YangMills.WilsonProof.NativeSupport.YM.MS.Menus.Glyph
/-!
# Coordinates in the physical composite system
 All finite weight spectra. Actual free Maxwell quotient.In particular no ghost gauge pin
 in physical statements! Basis leading over arbitrary Deck at all grades.Excludes address yet.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Theater
open Set Function Filter Finset Metric MeasureTheory Real Maxwell Labels
open Analysis Tensor Koszul Plane Landau Detect Detect.Mark Local.BV InnerProductSpace Submodule Momentum Local Woven Color Physical Menus
open Complex (I)
open scoped Topology ContDiff BigOperators RealInnerProductSpace
variable {G:Gauge}{h k n r:ℕ}{u:ℤ}{X:Law G}{B:Physical.Deck G} {p:Pol G}
variable (B)
variable {d:ℕ}
variable {i:Glyph B h}
lemma bossF (p:WickPol G): True:= trivial

-- horizon Λ.P
lemma readHeight (d:ℕ)(i:Glyph B d) : Daylight B d i=Rune B i:= Module.Basis.mk_apply ..
end YM.MS.Theater
