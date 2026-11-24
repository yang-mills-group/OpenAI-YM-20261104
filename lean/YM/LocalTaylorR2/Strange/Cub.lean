import YM.LocalTaylorR2.Strange.Pod
import YM.LocalTaylorR2.Kiln.Stargaze

/-! # All exponent-model pricing (vacuum path/principal including cubic etc.). -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Strange
open Exponent
open Function Filter Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Control Window Coat Footprint Raw Matter
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Stained Shield
open PhysicalNext PhysicalNext.Repeat Height Greenbelt Brim
open Gas Ursell Trees RG.Supply Org Roost Opera
open AnalyticBridge VerifiedReset Collection Extra.Iteration Match Song Refrain Geo Quotes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {P : Teller G}
variable {s μ C W : ℝ} {n : ℕ} {R R' : RG.Rep G f}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi}
variable (H : Cash W s μ L Q o C T R) {I : Cash W s μ L Q o C T R'}
open YM.RG01.Survive Port Candle
open Reel Mesh
-- E-only transports actual E symbol (including mask switches on that R ONLY). All others unaffected.
def cuboid (w:Reel.Scroll G f)(p:ℕ)(i:LogIndex c f): Port.Test T := match i with
| .inl (.inl i) => Reel.sprout H w (.inl (.inl i))
| _ => Exponent.iceberg H p i

def jetEngine (G:Gauge): Engine G where
  toObservatory := Exponent.astrolabe G
  plug H:= cuboid H
  fits H w J p:=by funext i; rcases i with (i|(i|(i|(i|(i|i)))))| (i|i|i)|i <;> try rfl
end YM.LocalTaylorR2.Strange
