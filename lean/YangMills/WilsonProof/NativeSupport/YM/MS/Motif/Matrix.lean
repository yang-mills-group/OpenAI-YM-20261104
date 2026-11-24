import YM.MS.Motif.Matrix
import YangMills.WilsonProof.NativeSupport.YM.MS.Motif.Beat
/-!
# Lie ring with supercommutative row coefficients

Signs [-1] explicit; matrix trace convention using G with fixed scaling. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Motif
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Garment Native
open scoped Topology ContDiff InnerProductSpace
variable {A:Type}{G:Gauge}{n:ℕ} {H:Rack G n} {b c:Bool}
local notation "S" => field ( Landau.parity ( A:=Arts.L n ) (C:=G.ColorIndex))
local infixl:67 " ⋄ "=> product S
variable {U F W:Mield G n}
theorem r_clock (i j k:G.ColorIndex): rune i j k= rune j k i:= by unfold rune; rw [scaled_tensor,scaled_tensor,Only.rotate] -- remove unwrap
private lemma earth {F:Rack G n}(p:Bool)(q:Bool): (-(cross p q:ℂ)) • F=-( (cross q p:ℂ) • F):= by rw [neg_smul,cross_comm]
end YM.MS.Motif
