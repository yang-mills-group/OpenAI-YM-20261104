import YM.MS.Motif.Pulp
import YangMills.WilsonProof.NativeSupport.YM.MS.Motif.Plateau
/-!
# Classical continuum action (before removing free terms)

Minimal system on all auxiliary dimensions. Hessian and pole reading below.
 Energies are log densities. Color real compact indices already fixed as in manuscript. 
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Motif
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Garment Native
open scoped Topology ContDiff InnerProductSpace
variable {G:Gauge} {n:ℕ}
local notation "S" => field ( Landau.parity ( A:=Arts.L n ) (C:=G.ColorIndex))
def core (G:Gauge)(n:ℕ)(z:ℂ): Rack G n:= (-(1/4):ℂ) • ∑ a:Arts.L n,∑ b:Arts.L n,sume (G:=G) (cur z a b) (cur z a b)
def ploy (G:Gauge)(z:ℂ) : Mob G:= fun n=> core G n z+ cape (applyS z G n)
-- classical gauge invariance according to Trill tested below.
local notation "g"=> cwave n G
local notation "Ω" => jaw G n
variable (z:ℂ)
-- δroot algebra
local notation "σ" => dot (applyS z G n)
local notation "Sg" => forge σ
lemma S_C : Sg g= Sc z G n:= funext fun i=> dot_call (none,i)
variable {u:Mield G n} {b:Bool}
end YM.MS.Motif
