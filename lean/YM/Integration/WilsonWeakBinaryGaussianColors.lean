import YM.Integration.WilsonMeasuredOriginalPeriodWord
import YM.Integration.WilsonOriginalThreeGaussianReturn

/-! At the recorded period the ordinary physical panel and the original
Gaussian program receive identical vacuum, marked words and Laurent grades. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonWeakBinaryGaussianColors
open Lattice RG Wilson Marker Multi QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Sunrise
open Comparison.RG02 FVA1Physical.TwoReset AllOrder AllOrder.Floe
open scoped BigOperators Classical
variable {G:Gauge}{n:Side}{V I X:Type}[DecidableEq V]
    {P:Passport n V}{J:Census V}(M:I→Row P J G X)(w:V→ℕ)
    (q:I→ℂ)(L:Layout G)(tape:Finset Age)

theorem original :
    Air.craft M q w L tape = QuadraticLocal.Fk.grant L tape (copyColor (f:=n) dvd_rfl M w q L tape) := by
  change Bulk.Colors.mk _ _ _=Bulk.Colors.mk _ _ _
  congr 1
  funext s
  exact (WilsonMeasuredOriginalPeriodWord.marked M w q L tape s).symm

end YM.Integration.WilsonWeakBinaryGaussianColors
end
