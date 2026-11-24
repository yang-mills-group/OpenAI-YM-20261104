import YM.MS.Theater.HoloK
import YangMills.WilsonProof.NativeSupport.YM.MS.Theater.Place
import YangMills.WilsonProof.NativeSupport.YM.MS.Lifting.Span
/-!
# Projection & G action.Color on Taylor.Offshell clockiness
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Theater
open Set Function Filter Finset Metric MeasureTheory Real Maxwell Labels
open Analysis Tensor Koszul Plane Landau Detect Detect.Mark Local.BV InnerProductSpace Submodule Momentum Local Woven Color
open Complex (I)
open scoped Topology ContDiff BigOperators RealInnerProductSpace
variable {G:Gauge}{h k n r:ℕ}{v:ℤ}{p q:Pol G}{F H:Law G}{f:Local.BV.Grade G}{J:Type}
local notation "KΩ"=> hands G
local notation "ζ"=> Koszul.mono
local infix:70 " ⋆ "=> product KΩ
variable (u:G.El)
end YM.MS.Theater
