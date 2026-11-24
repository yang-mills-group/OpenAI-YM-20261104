import YM.MS.Theater.DataK
import YangMills.WilsonProof.NativeSupport.YM.MS.Theater.BrightK
import YM.Next.MAXWELL.Algebra
import YM.Next.MAXWELL.Covariance
/-!
# Picking the explicit isomorphisms (real; use complex-linear extension later).
Use of elimination on quotients restricted with §.W.Label.Point.B. keep higher free basis.Loops.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Theater
open Set Function Filter Finset Metric MeasureTheory Real Maxwell Labels
open Analysis Tensor Koszul Plane Landau Detect Detect.Mark Local.BV InnerProductSpace Submodule Momentum Local Woven Color Physical
open Complex (I)
open scoped Topology ContDiff BigOperators RealInnerProductSpace
variable {G:Gauge}{h k n r:ℕ}{u:ℤ}{X:Law G}{B:Physical.Deck G}
local notation "KΩ"=> hands G
local notation "ζ"=> Koszul.mono
-- image from real version.Use both Φ choices.Lit basis.A.
variable (B)
local notation "Vκ"=> Resume B h r
abbrev crew (x:B.carries h r):= reduceEq ( Vκ x ).val
-- solve to manifold. exclude empty.Costas
-- installs financial basis.
-- fix ambiguities.W.Loops.
end YM.MS.Theater
