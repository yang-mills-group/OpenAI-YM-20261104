import YM.MS.Motif.Pulp
import YM.MS.Motif.Shift

set_option autoImplicit false
noncomputable section
namespace YM.MS.Motif
open Set Filter Function Finset MeasureTheory Metric Real
open Plane Koszul Heat Flux Landau Arts Book Convolve
open Literal
open scoped Topology ContDiff InnerProductSpace
variable {G:Gauge} {n:ℕ}
local notation "S"=> field ( Landau.parity ( A:=Arts.L n ) (C:=G.ColorIndex))
def quill (i j:Arts.L n): Mield G n:= jaw G n (A n G i) ( A n G j )
def top3 (G:Gauge)(n:ℕ): Rack G n:= (-(1/4):ℂ) • ∑ i:Arts.L n,∑ j:Arts.L n,(sume (G:=G) (F₀ i j) ( quill i j )+sume ( quill i j ) ( F₀ i j ))
def top4 (G:Gauge)(n:ℕ): Rack G n:= (-(1/4):ℂ) • ∑ i:Arts.L n,∑ j:Arts.L n, sume ( G:=G) (quill i j) ( quill i j )
def blazeV (G:Gauge)(n:ℕ): Chan G n→ Rack G n
 | (some p,i)=> jaw G n (A n G p) (cwave n G) i
 | (none,i)=> Sc 1 G n i
def B₁ (G:Gauge) :Mob G:= fun n=> top3 G n+ cape ( blazeV G n )
def B₂ (G:Gauge) : Mob G:= top4 G
def χ (G: Gauge) : Box (Mob G):= .single 1 (B₁ G)+.single 2 (B₂ G)
abbrev pulseX (G:Gauge): T (Mob G):= linear (Mob G) (χ G)
end YM.MS.Motif
