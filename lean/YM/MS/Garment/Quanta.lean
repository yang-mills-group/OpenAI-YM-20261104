import YM.MS.Arts.Range

set_option autoImplicit false
noncomputable section
namespace YM.MS.Garment.Wave
open Function Set Filter Finset MeasureTheory Real Plane Koszul Flux Landau Arts
open Momentum Metric
open scoped Topology ContDiff
variable {G:Gauge} {m:ℕ} {l:Legs (Shore G m)}
def slice (l:Legs (Shore G m)): Mob G →ₗ[ℂ] ℂ:= (LinearMap.proj l) ∘ₗ (LinearMap.proj m)
end YM.MS.Garment.Wave
