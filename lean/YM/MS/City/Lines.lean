import YM.MS.Landau

set_option autoImplicit false
noncomputable section
namespace YM.MS.City
open Function Filter Set Finset Plane Koszul Flux MeasureTheory
open Landau Momentum Real
open Complex (I)
open scoped Topology ContDiff
variable {D:Type} [Fintype D] [DecidableEq D]
abbrev YMflow (D:Type) := Flux (Atom D) (Momentum D) ℂ
def brush (r:ℝ)(p:Momentum D) := r^3*exp (-(r^2*p.sq))
def L0 (r:ℝ): YMflow D
 | (some i,false),(some j,false),p=> ((brush r p*precision i j p :ℝ):ℂ)
 | (some i,true),(none,false),p=> I*(brush r p*(p.sq*p i):ℝ)
 | (none,false),(some i,true),p=> I*(brush r p*(p.sq*p i):ℝ)
 | _,_,_=> 0
end YM.MS.City
