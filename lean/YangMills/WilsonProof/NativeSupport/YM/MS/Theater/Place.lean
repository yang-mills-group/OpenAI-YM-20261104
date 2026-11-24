import YM.MS.Theater.Place
import YM.MS.Theater.Value
import YM.MS.Theater.Grip
import YM.MS.Theater.Pen
import YM.MS.Theater.Bread
import YM.MS.Theater.RakeA
import YM.MS.Theater.Well
import YangMills.WilsonProof.NativeSupport.YM.MS.Local.Curls
import YM.MS.Theater.Life
import YM.MS.Theater.Eq
import YM.MS.Theater.Radium
import YM.MS.Theater.Pave
import YM.MS.Theater.Scale
import YM.MS.Theater.Seat
import YangMills.WilsonProof.NativeSupport.YM.MS.Local.Labels
import YangMills.WilsonProof.NativeSupport.YM.MS.Local.Fac
/-!
# Pre-color reach of Φ
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Theater
open Set Function Filter Finset Metric MeasureTheory Real Maxwell Labels
open Analysis Tensor Koszul Plane Landau Detect Detect.Mark Local.BV InnerProductSpace Submodule Momentum Local Woven
open Complex (I)
open scoped Topology ContDiff BigOperators RealInnerProductSpace
variable {G:Gauge}{h k n r:ℕ}{u x v:ℤ}{p q:Pol G}{F H:Law G}{f:Local.BV.Grade G}
local notation "KΩ"=> hands G
local notation "ζ"=> Koszul.mono
local infix:70 " ⋆ "=> product KΩ
lemma ontoU (p: Fin r→ Witness G h): True := trivial -- remove
end YM.MS.Theater
