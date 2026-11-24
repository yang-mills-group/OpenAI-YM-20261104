import YM.MS.Motif.Vary
import YangMills.WilsonProof.NativeSupport.YM.MS.Motif.Binary
/-!
# Derivative and letters in local Row basis
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Motif
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire
open scoped Topology ContDiff
variable {A P R B:Type}[CommRing R][AddCommGroup P] {p:Sector A}{b c:Bool}{u f g:Row A P R}{i:A}
local infixl:67 "⋄"=> product (field p)
lemma momZero (s:P→+R) {r:R}: moment (P:=P) s (coin r : Row A P R)=0:= by funext l; cases l <;> simp [moon,net,coin] -- fix s binder
variable [DecidableEq A]
end YM.MS.Motif
