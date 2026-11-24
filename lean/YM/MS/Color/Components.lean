import YM.Gauge.Colors
import YM.MS.Properties
import YM.MS.Color.Only

set_option autoImplicit false
noncomputable section
namespace YM.MS.Landau
open Function Filter Set Finset Only Koszul Plane Gauge
open scoped Topology InnerProductSpace ContDiff
variable {G: Gauge}
abbrev CI (G:Gauge):= G.ColorIndex
end YM.MS.Landau
